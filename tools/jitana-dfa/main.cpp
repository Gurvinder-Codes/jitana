#include <algorithm>
#include <cctype>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <stdexcept>
#include <string>
#include <vector>

#include <boost/filesystem.hpp>
#include <boost/optional.hpp>
#include <boost/system/error_code.hpp>

#include <boost/graph/graph_traits.hpp>
#include <boost/dynamic_bitset.hpp>

#include <jitana/jitana.hpp>
#include <jitana/analysis/variable_liveness.hpp>
#include <jitana/analysis/variable_reuse.hpp>
#include <jitana/analysis/taint_analysis.hpp>
#include <jitana/analysis/interproc_param_taint.hpp>

using namespace jitana;

static constexpr uint8_t LOADER_ID = 100;
namespace fs = boost::filesystem;

static std::string method_id_string(const analysis::dfa::MethodId& mid)
{
    std::ostringstream os;
    os << mid.type << "." << mid.name << mid.descriptor;
    return os.str();
}

struct TempDirGuard {
    explicit TempDirGuard(fs::path p) : path(std::move(p)) {}
    ~TempDirGuard()
    {
        if (!path.empty()) {
            boost::system::error_code ec;
            fs::remove_all(path, ec);
        }
    }

    fs::path path;
};

// Wire a single loader and populate classes.
static bool wire_loader(virtual_machine& vm,
                        const std::vector<std::string>& dex_files,
                        const std::string& label, bool quiet) {
    if (dex_files.empty()) {
        std::cerr << "[-] No DEX files provided to wire loader.\n";
        return false;
    }
    class_loader loader(LOADER_ID, "DFALoader", dex_files.begin(),
                        dex_files.end());
    vm.add_loader(loader);

    // Populate the class graph (available on most Jitana trees).
    if (!vm.load_all_classes(LOADER_ID)) {
        // Suppress warning when quiet - this is just informational
        if (!quiet) {
            std::cerr << "[!] Some classes could not be loaded from " << label
                      << " (likely missing dependencies); continuing with those "
                         "that succeeded.\n";
        }
    }

    if (!quiet) {
        std::cout << "[+] Loader wired for: " << label << "\n";
    }
    return true;
}

static class_vertex_descriptor
ensure_placeholder_class(virtual_machine& vm, const jvm_type_hdl& type_hdl) {
    if (auto existing = vm.find_class(type_hdl, false)) {
        return *existing;
    }

    class_vertex_property prop{};
    prop.jvm_hdl = type_hdl;
    prop.access_flags = acc_public;
    auto cv = add_vertex(prop, vm.classes());
    vm.classes()[boost::graph_bundle].jvm_hdl_to_vertex[type_hdl] = cv;
    return cv;
}

static void seed_placeholder_classes(virtual_machine& vm) {
    static const char* kBootstrapTypes[] = {
        // Java core
        "Ljava/lang/Object;",
        "Ljava/lang/Class;",
        "Ljava/lang/String;",
        "Ljava/lang/System;",
        "Ljava/lang/Runtime;",
        "Ljava/lang/ProcessBuilder;",
        "Ljava/lang/ClassLoader;",
        // Java I/O
        "Ljava/io/PrintStream;",
        "Ljava/io/FileOutputStream;",
        "Ljava/io/FileInputStream;",
        "Ljava/io/FileWriter;",
        "Ljava/io/RandomAccessFile;",
        // Java networking
        "Ljava/net/URL;",
        "Ljava/net/Socket;",
        "Ljava/net/HttpURLConnection;",
        // Android telephony
        "Landroid/telephony/TelephonyManager;",
        "Landroid/telephony/SmsManager;",
        // Android UI / WebView
        "Landroid/webkit/WebView;",
        // Android logging
        "Landroid/util/Log;",
        // Android SQLite
        "Landroid/database/sqlite/SQLiteDatabase;",
        // JNDI
        "Ljavax/naming/InitialContext;",
        // Android inter-app communication
        "Landroid/content/Context;",
    };

    for (const char* desc : kBootstrapTypes) {
        ensure_placeholder_class(vm, {class_loader_hdl{LOADER_ID}, desc});
    }
}

struct DexSources {
    std::vector<std::string> files;
    boost::optional<TempDirGuard> temp_guard;
};

static fs::path make_temp_directory()
{
    auto base = fs::temp_directory_path()
            / fs::unique_path("jitana-dfa-%%%%%%%%");
    if (!fs::create_directories(base)) {
        throw std::runtime_error("failed to create temp directory");
    }
    return base;
}

static void extract_apk_classes(const fs::path& apk_path,
                                const fs::path& out_dir)
{
    std::string cmd = "unzip -qq -o \"" + apk_path.string()
            + "\" \"classes*.dex\" -d \"" + out_dir.string() + "\"";
    int rc = std::system(cmd.c_str());
    if (rc != 0) {
        throw std::runtime_error("failed to extract classes*.dex from APK");
    }
}

static DexSources prepare_dex_sources(const std::string& input_path)
{
    DexSources sources;
    fs::path in_path(input_path);
    if (!fs::exists(in_path)) {
        throw std::runtime_error("input path does not exist: " + input_path);
    }

    auto ext = in_path.extension().string();
    std::transform(ext.begin(), ext.end(), ext.begin(),
                   [](unsigned char c) { return std::tolower(c); });

    if (ext == ".dex") {
        sources.files.push_back(in_path.string());
        return sources;
    }

    if (ext == ".apk") {
        auto temp_dir = make_temp_directory();
        extract_apk_classes(in_path, temp_dir);

        std::vector<std::string> dex_files;
        for (const auto& entry : fs::directory_iterator(temp_dir)) {
            if (!entry.is_regular_file()) {
                continue;
            }
            auto filename = entry.path().filename().string();
            auto dex_ext = entry.path().extension().string();
            std::transform(filename.begin(), filename.end(), filename.begin(),
                           [](unsigned char c) { return std::tolower(c); });
            std::transform(dex_ext.begin(), dex_ext.end(), dex_ext.begin(),
                           [](unsigned char c) { return std::tolower(c); });
            if (filename.rfind("classes", 0) == 0 && dex_ext == ".dex") {
                dex_files.push_back(entry.path().string());
            }
        }

        if (dex_files.empty()) {
            throw std::runtime_error(
                    "APK did not contain any classes*.dex files");
        }
        std::sort(dex_files.begin(), dex_files.end());
        sources.files = std::move(dex_files);
        sources.temp_guard.emplace(temp_dir);
        return sources;
    }

    throw std::runtime_error("unsupported input type: " + input_path);
}

// ---------------------------------------------------------------------------
// JVM descriptor → Java-style helpers
// ---------------------------------------------------------------------------

// Convert a single JVM type descriptor to a readable Java type name.
// "Ljava/lang/String;" -> "String"   "[I" -> "int[]"   "I" -> "int"
static std::string type_desc_to_java(const std::string& d, std::size_t pos = 0)
{
    int arrays = 0;
    while (pos < d.size() && d[pos] == '[') {
        ++arrays;
        ++pos;
    }
    if (pos >= d.size()) return d;

    std::string base;
    switch (d[pos]) {
    case 'B': base = "byte";    break;
    case 'C': base = "char";    break;
    case 'D': base = "double";  break;
    case 'F': base = "float";   break;
    case 'I': base = "int";     break;
    case 'J': base = "long";    break;
    case 'S': base = "short";   break;
    case 'V': base = "void";    break;
    case 'Z': base = "boolean"; break;
    case 'L': {
        auto end = d.find(';', pos + 1);
        auto inner = (end == std::string::npos)
                         ? d.substr(pos + 1)
                         : d.substr(pos + 1, end - pos - 1);
        auto slash = inner.rfind('/');
        base = (slash == std::string::npos) ? inner : inner.substr(slash + 1);
        break;
    }
    default:
        base = d.substr(pos, 1);
    }
    for (int i = 0; i < arrays; ++i) base += "[]";
    return base;
}

// Convert a JVM method descriptor to Java-style.
// "(Ljava/lang/String;I)Ljava/lang/Process;" -> "(String, int): Process"
static std::string method_desc_to_java(const std::string& desc)
{
    if (desc.empty() || desc[0] != '(') return desc;
    auto close = desc.find(')');
    if (close == std::string::npos) return desc;

    // Parse parameter types
    std::vector<std::string> params;
    std::size_t i = 1;
    while (i < close) {
        std::size_t start = i;
        while (i < close && desc[i] == '[') ++i;  // skip array dims
        if (i >= close) break;
        if (desc[i] == 'L') {
            auto end = desc.find(';', i);
            if (end == std::string::npos || end >= close) break;
            params.push_back(type_desc_to_java(desc, start));
            i = end + 1;
        } else {
            params.push_back(type_desc_to_java(desc, start));
            ++i;
        }
    }

    std::string ret = type_desc_to_java(desc, close + 1);

    std::string result = "(";
    for (std::size_t k = 0; k < params.size(); ++k) {
        if (k > 0) result += ", ";
        result += params[k];
    }
    result += "): ";
    result += ret;
    return result;
}

// Full Java class path from JVM type descriptor.
// "Ljava/lang/String;" -> "java.lang.String"
static std::string type_desc_to_full_java(const std::string& desc)
{
    std::string s = desc;
    if (s.size() >= 2 && s[0] == 'L' && s.back() == ';') {
        s = s.substr(1, s.size() - 2);
    }
    for (char& c : s) {
        if (c == '/') c = '.';
    }
    return s;
}

// Simple class name only.  "Ljava/lang/String;" -> "String"
static std::string type_desc_to_simple(const std::string& desc)
{
    auto full = type_desc_to_full_java(desc);
    auto dot = full.rfind('.');
    return (dot == std::string::npos) ? full : full.substr(dot + 1);
}

// Package only.  "Ljava/lang/String;" -> "java.lang"
static std::string type_desc_to_package(const std::string& desc)
{
    auto full = type_desc_to_full_java(desc);
    auto dot = full.rfind('.');
    return (dot == std::string::npos) ? "" : full.substr(0, dot);
}

// Human-readable method name.  "<init>" -> "new"  "<clinit>" -> "[static init]"
static std::string readable_method_name(const std::string& name)
{
    if (name == "<init>")   return "new";
    if (name == "<clinit>") return "[static init]";
    return name;
}

// ---------------------------------------------------------------------------
// DOT output helpers
// ---------------------------------------------------------------------------

static std::string dot_escape(const std::string& s)
{
    std::string out;
    out.reserve(s.size());
    for (char c : s) {
        if (c == '"' || c == '\\') out.push_back('\\');
        out.push_back(c);
    }
    return out;
}

// HTML-escapes a string for use inside GraphViz HTML labels.
static std::string html_escape(const std::string& s)
{
    std::string out;
    out.reserve(s.size() + 8);
    for (char c : s) {
        switch (c) {
        case '&': out += "&amp;";  break;
        case '<': out += "&lt;";   break;
        case '>': out += "&gt;";   break;
        case '"': out += "&quot;"; break;
        default:  out.push_back(c);
        }
    }
    return out;
}

// Returns Java-style parameter type names from a JVM method descriptor.
// "(Ljava/lang/String;I[B)V" -> {"String", "int", "byte[]"}
static std::vector<std::string> get_param_types(const std::string& desc)
{
    std::vector<std::string> result;
    if (desc.empty() || desc[0] != '(') return result;
    auto close = desc.find(')');
    if (close == std::string::npos) return result;
    std::size_t i = 1;
    while (i < close) {
        std::size_t start = i;
        while (i < close && desc[i] == '[') ++i;
        if (i >= close) break;
        if (desc[i] == 'L') {
            auto end = desc.find(';', i);
            if (end == std::string::npos || end >= close) break;
            result.push_back(type_desc_to_java(desc, start));
            i = end + 1;
        } else {
            result.push_back(type_desc_to_java(desc, start));
            ++i;
        }
    }
    return result;
}

// HTML-table node label.  Example rendering:
//
//  ┌──────────────────────────────┐
//  │  ClassName                   │  ← coloured header
//  ├──────────────────────────────┤
//  │  com.example.package         │  ← small grey package row
//  ├──────────────────────────────┤
//  │  methodName(Type, …): Ret    │  ← method signature
//  └──────────────────────────────┘
static std::string node_html_label(const analysis::dfa::MethodId& mid,
                                   const std::string& hdr_bg,
                                   const std::string& hdr_fg)
{
    auto cls  = html_escape(type_desc_to_simple(mid.type.descriptor));
    auto pkg  = html_escape(type_desc_to_package(mid.type.descriptor));
    auto meth = html_escape(readable_method_name(mid.name)
                            + method_desc_to_java(mid.descriptor));

    std::string out;
    out += "<TABLE BORDER=\"0\" CELLBORDER=\"1\" CELLSPACING=\"0\""
           " CELLPADDING=\"5\" BGCOLOR=\"white\">";
    out += "<TR><TD BGCOLOR=\"" + hdr_bg + "\" ALIGN=\"CENTER\">"
           "<FONT COLOR=\"" + hdr_fg + "\"><B>" + cls + "</B></FONT></TD></TR>";
    if (!pkg.empty()) {
        out += "<TR><TD ALIGN=\"LEFT\">"
               "<FONT POINT-SIZE=\"8\" COLOR=\"#666666\">" + pkg
               + "</FONT></TD></TR>";
    }
    out += "<TR><TD ALIGN=\"LEFT\">" + meth + "</TD></TR>";
    out += "</TABLE>";
    return out;
}

// Tooltip: fully-qualified Java-style name for hover text.
static std::string node_tooltip(const analysis::dfa::MethodId& mid)
{
    std::string full = type_desc_to_full_java(mid.type.descriptor);
    std::string meth = readable_method_name(mid.name)
                     + method_desc_to_java(mid.descriptor);
    return dot_escape(full + "." + meth);
}

// ---------------------------------------------------------------------------

static void write_taint_graph(const std::string& graph_out,
                              const analysis::dfa::InterprocParamResult& interproc)
{
    std::ofstream ofs(graph_out);
    if (!ofs) {
        std::cerr << "[-] Failed to open graph output file: " << graph_out
                  << "\n";
        return;
    }

    // Build unique caller and sink node lists.
    std::vector<analysis::dfa::MethodId> caller_list, sink_list;
    std::unordered_map<analysis::dfa::MethodId, std::size_t,
                       analysis::dfa::MethodIdHash>
            caller_idx, sink_idx;

    // One merged edge per (caller, sink) pair: union of tainted args and all
    // call-site offsets so parallel edges from the same caller don't clutter
    // the graph.
    struct MergedEdge {
        std::size_t ci, si;
        std::set<int> tainted_args;
        std::vector<uint32_t> offsets;
    };
    std::map<std::pair<std::size_t, std::size_t>, MergedEdge> edge_map;

    for (const auto& hit : interproc.sink_hits) {
        std::size_t ci, si;
        {
            auto it = caller_idx.find(hit.caller);
            if (it == caller_idx.end()) {
                ci = caller_list.size();
                caller_idx[hit.caller] = ci;
                caller_list.push_back(hit.caller);
            } else {
                ci = it->second;
            }
        }
        {
            auto it = sink_idx.find(hit.callee);
            if (it == sink_idx.end()) {
                si = sink_list.size();
                sink_idx[hit.callee] = si;
                sink_list.push_back(hit.callee);
            } else {
                si = it->second;
            }
        }
        auto key = std::make_pair(ci, si);
        auto& me = edge_map[key];
        me.ci = ci;
        me.si = si;
        for (std::size_t a : hit.tainted_args) {
            me.tainted_args.insert(static_cast<int>(a));
        }
        me.offsets.push_back(hit.offset);
    }

    // Threshold: use compact sink-grouped layout for large graphs.
    static constexpr std::size_t LARGE_GRAPH_THRESHOLD = 15;
    const bool large_graph = (caller_list.size() > LARGE_GRAPH_THRESHOLD);

    // Group callers by package (small-graph layout only).
    std::map<std::string, std::vector<std::size_t>> pkg_groups;
    if (!large_graph) {
        for (std::size_t i = 0; i < caller_list.size(); ++i) {
            pkg_groups[type_desc_to_package(caller_list[i].type.descriptor)]
                    .push_back(i);
        }
    }
    const bool use_pkg_clusters = (!large_graph && pkg_groups.size() > 1);

    // For large graphs: map each sink index → callers that reach it.
    // A caller reaching multiple sinks is placed in EACH sink's sub-cluster
    // (using unique node IDs g{ci}_{si}) so every edge stays within its
    // sink's visual group and no arrows appear to come from nowhere.
    std::map<std::size_t, std::vector<std::size_t>> sink_caller_groups;
    if (large_graph) {
        for (const auto& kv : edge_map) {
            sink_caller_groups[kv.second.si].push_back(kv.second.ci);
        }
    }

    // -----------------------------------------------------------------------
    ofs << "digraph TaintGraph {\n";
    ofs << "  graph ["
           "label=\"Parameter Taint Analysis\\n"
           "Tainted method parameters flow from app methods to dangerous sink"
           " APIs\","
           " labelloc=t, fontsize=14, fontname=\"Helvetica\","
           " bgcolor=\"#fafafa\", pad=\"0.5\""
           "];\n";
    ofs << "  rankdir=" << (large_graph ? "LR" : "TB") << ";\n";
    ofs << "  nodesep=" << (large_graph ? "0.4" : "0.8") << ";\n";
    ofs << "  ranksep=" << (large_graph ? "2.0" : "1.4") << ";\n";
    ofs << "  node [shape=none, fontname=\"Helvetica\", fontsize=10];\n";
    ofs << "  edge [fontname=\"Helvetica\", fontsize=9, penwidth=1.5];\n";

    // -- Cluster: Callers ----------------------------------------------------
    ofs << "  subgraph cluster_callers {\n";
    ofs << "    label=\"Methods with tainted parameters\";\n";
    ofs << "    fontname=\"Helvetica\"; fontsize=12; fontcolor=\"#1a5276\";\n";
    ofs << "    style=rounded; fillcolor=\"#eaf4fb\";"
           " color=\"#2471a3\"; penwidth=2;\n";

    if (large_graph) {
        // Flat layout: emit all g{ci}_{si} nodes directly inside
        // cluster_callers without sub-clusters.  GraphViz is free to
        // position each node near its target sink, keeping edges short
        // and horizontal.  Sub-clusters caused tall stacks where nodes
        // at the top/bottom had steeply diagonal edges that exited the
        // viewport, making them appear unconnected.
        for (const auto& kv : sink_caller_groups) {
            std::size_t si = kv.first;
            for (std::size_t ci : kv.second) {
                const auto& mid = caller_list[ci];
                ofs << "    g" << ci << "_" << si
                    << " [label=<"
                    << node_html_label(mid, "#1a5276", "white")
                    << ">, tooltip=\"" << node_tooltip(mid) << "\"];\n";
            }
        }
    } else if (use_pkg_clusters) {
        int pkg_seq = 0;
        for (const auto& pkv : pkg_groups) {
            const auto& label = pkv.first.empty() ? "(default package)"
                                                   : pkv.first;
            ofs << "    subgraph cluster_pkg" << pkg_seq++ << " {\n";
            ofs << "      label=\"" << dot_escape(label) << "\";\n";
            ofs << "      fontsize=10; fontcolor=\"#1a5276\";\n";
            ofs << "      style=dashed; color=\"#85c1e9\";"
                   " fillcolor=\"#d6eaf8\";\n";
            for (std::size_t i : pkv.second) {
                const auto& mid = caller_list[i];
                ofs << "      c" << i
                    << " [label=<"
                    << node_html_label(mid, "#1a5276", "white")
                    << ">, tooltip=\"" << node_tooltip(mid) << "\"];\n";
            }
            ofs << "    }\n";
        }
    } else {
        for (std::size_t i = 0; i < caller_list.size(); ++i) {
            const auto& mid = caller_list[i];
            ofs << "    c" << i
                << " [label=<"
                << node_html_label(mid, "#1a5276", "white")
                << ">, tooltip=\"" << node_tooltip(mid) << "\"];\n";
        }
    }
    ofs << "  }\n\n";

    // -- Cluster: Sinks ------------------------------------------------------
    ofs << "  subgraph cluster_sinks {\n";
    ofs << "    label=\"Dangerous sink APIs\";\n";
    ofs << "    fontname=\"Helvetica\"; fontsize=12; fontcolor=\"#922b21\";\n";
    ofs << "    style=rounded; fillcolor=\"#fdedec\";"
           " color=\"#922b21\"; penwidth=2;\n";
    for (std::size_t i = 0; i < sink_list.size(); ++i) {
        const auto& mid = sink_list[i];
        ofs << "    s" << i
            << " [label=<"
            << node_html_label(mid, "#7b241c", "white")
            << ">, tooltip=\"" << node_tooltip(mid) << "\"];\n";
    }
    ofs << "  }\n\n";

    // -- Edges ---------------------------------------------------------------
    // One edge per (caller, sink) pair.  Label shows the union of all tainted
    // argument indices with their type (from the sink's descriptor), plus a
    // call-site count or the single offset when there is only one.
    for (const auto& kv : edge_map) {
        const auto& me = kv.second;
        const auto& sink_mid = sink_list[me.si];
        auto param_types = get_param_types(sink_mid.descriptor);

        std::ostringstream elabel;
        bool first_arg = true;
        for (int a : me.tainted_args) {
            if (!first_arg) elabel << "\\n";
            first_arg = false;

            // Best-effort type annotation:
            //   arg 0 = "this" for virtual calls (not in descriptor)
            //   arg k = param_types[k-1] for virtual, param_types[k] for static
            // We can't distinguish static vs. virtual from MethodId alone, so
            // show the most informative guess: treat arg 0 as "this" and
            // map arg k ≥ 1 to param_types[k-1].
            std::string type_hint;
            if (a == 0) {
                type_hint = " (this)";
            } else {
                auto idx = static_cast<std::size_t>(a - 1);
                if (idx < param_types.size()) {
                    type_hint = " (" + param_types[idx] + ")";
                }
            }
            elabel << "arg" << a << type_hint << " tainted";
        }

        if (me.offsets.size() == 1) {
            elabel << "\\n@ 0x" << std::hex << me.offsets[0] << std::dec;
        } else {
            elabel << "\\n" << me.offsets.size() << " call sites";
        }

        if (large_graph) {
            ofs << "  g" << me.ci << "_" << me.si << " -> s" << me.si;
        } else {
            ofs << "  c" << me.ci << " -> s" << me.si;
        }
        ofs << " [label=\"" << elabel.str() << "\","
               " color=\"#e74c3c\", fontcolor=\"#922b21\","
               " arrowhead=vee];\n";
    }

    // -- Legend --------------------------------------------------------------
    ofs << "\n  subgraph cluster_legend {\n";
    ofs << "    label=\"Legend\"; style=rounded; fontsize=9;\n";
    ofs << "    fontname=\"Helvetica\"; color=\"#aaaaaa\"; fillcolor=\"#f5f5f5\";\n";
    ofs << "    node [shape=plaintext, fontsize=9, fontname=\"Helvetica\"];\n";
    ofs << "    leg [label="
           "\"Blue header = app method that passes tainted param to a sink\\n"
           "Red header  = dangerous API (sink)\\n"
           "Arrow label = tainted argument index and type\\n"
           "  arg 0 = this (virtual), arg 1 = first param, ...\"];\n";
    ofs << "  }\n";
    ofs << "}\n";

    ofs.close();
    std::cerr << "[+] Wrote taint call graph to "
              << fs::absolute(graph_out).string() << " ("
              << interproc.sink_hits.size() << " sink hit(s))\n";
}

int main(int argc, char** argv) {
    try {
        std::string graph_out;
        bool interproc_only = false;
        bool quiet = false;
        std::vector<std::string> positional;
        for (int i = 1; i < argc; ++i) {
            std::string arg = argv[i];
            if (arg == "--taint-graph" && i + 1 < argc) {
                graph_out = argv[++i];
                continue;
            }
            if (arg == "--interproc-only") {
                interproc_only = true;
                continue;
            }
            if (arg == "--quiet" || arg == "-q") {
                quiet = true;
                continue;
            }
            positional.push_back(arg);
        }
        if (positional.empty()) {
            std::cerr << "Usage: " << argv[0]
                      << " [--quiet|-q] [--interproc-only]"
                         " [--taint-graph FILE] <file.dex|app.apk>\n"
                      << "  --quiet, -q        Suppress verbose output"
                         " (taint graph still written if --taint-graph given).\n"
                      << "  --interproc-only   Skip per-method taint output;"
                         " run interprocedural analysis only.\n"
                      << "  --taint-graph FILE Write DOT graph of taint flows"
                         " to sinks to FILE.\n";
            return 2;
        }
        const std::string input_path = positional.front();

        auto sources = prepare_dex_sources(input_path);

        virtual_machine vm;
        seed_placeholder_classes(vm);

        if (!wire_loader(vm, sources.files, input_path, quiet)) {
            std::cerr << "[-] Failed to wire loader.\n";
            return 1;
        }

        const auto& mg = vm.methods();
        std::size_t analyzed = 0;

        // --- Per-method intraprocedural taint (optional) ---
        if (!interproc_only) {
            for (auto mvp = vertices(mg); mvp.first != mvp.second; ++mvp.first) {
                const auto mv = *mvp.first;
                const auto& method = mg[mv];

                if (num_vertices(method.insns) == 0) {
                    continue;
                }

                auto T = analysis::dfa::run_taint(vm, mv);
                boost::dynamic_bitset<> tainted_union(T.reg_domain);
                for (const auto& bits : T.TAINT_IN) {
                    tainted_union |= bits;
                }
                for (const auto& bits : T.TAINT_OUT) {
                    tainted_union |= bits;
                }
                bool has_taint = tainted_union.any();
                bool has_tainted_use = false;
                if (has_taint) {
                    const auto& ig = mg[mv].insns;
                    const auto order = analysis::dfa::run_liveness(vm, mv).order;
                    for (std::size_t i = 0; i < order.size() && !has_tainted_use;
                         ++i) {
                        for (const auto& reg : uses(ig[order[i]].insn)) {
                            if (!reg.valid() || reg.is_result()
                                || reg.is_exception()) {
                                continue;
                            }
                            auto raw = static_cast<int32_t>(reg);
                            if (raw < 0) {
                                continue;
                            }
                            auto idx = static_cast<std::size_t>(raw);
                            if (idx < T.reg_domain && tainted_union.test(idx)) {
                                has_tainted_use = true;
                            }
                        }
                    }
                }
                if (!has_taint || !has_tainted_use) {
                    continue;
                }

                auto L = analysis::dfa::run_liveness(vm, mv);
                auto reuse = analysis::dfa::run_variable_reuse(vm, mv, L);

                ++analyzed;
                if (!quiet) {
                    std::cout << "\n[+] Method #" << analyzed << ": "
                              << method.jvm_hdl << "\n";
                    std::cout << "    Register domain size : " << L.reg_domain
                              << "\n";
                    std::cout << "    Tainted registers (union of IN/OUT): ";
                    bool first_reg = true;
                    for (std::size_t r = 0; r < T.reg_domain; ++r) {
                        if (tainted_union.test(r)) {
                            if (!first_reg) {
                                std::cout << ", ";
                            }
                            std::cout << "v" << r;
                            first_reg = false;
                        }
                    }
                    if (first_reg) {
                        std::cout << "none";
                    }
                    std::cout << "\n";
                }
            }
        }

        // --- Interprocedural parameter taint (always runs) ---
        analysis::dfa::InterprocParamConfig ipc_cfg;
        auto interproc = analysis::dfa::run_interproc_param_taint(vm, ipc_cfg);

        if (!quiet) {
            if (interproc_only) {
                std::cout << "\n[+] Interprocedural taint analysis complete.\n";
            }

            // Print method summaries with non-empty return dependencies.
            std::vector<std::pair<std::string, analysis::dfa::MethodSummary>>
                    sorted;
            sorted.reserve(interproc.summaries.size());
            for (const auto& kv : interproc.summaries) {
                if (!kv.second.return_dep.any()) {
                    continue;
                }
                std::ostringstream os;
                os << kv.first.type << "." << kv.first.name
                   << kv.first.descriptor;
                sorted.emplace_back(os.str(), kv.second);
            }
            std::sort(sorted.begin(), sorted.end(),
                      [](const auto& a, const auto& b) {
                          return a.first < b.first;
                      });
            if (!sorted.empty()) {
                std::cout << "\n[+] Interprocedural parameter taint summaries\n";
                for (const auto& item : sorted) {
                    std::cout << "    " << item.first << " ReturnDependsOn = {";
                    bool first = true;
                    for (std::size_t i = 0; i < item.second.return_dep.size();
                         ++i) {
                        if (item.second.return_dep.test(i)) {
                            if (!first) {
                                std::cout << ",";
                            }
                            std::cout << i;
                            first = false;
                        }
                    }
                    std::cout << "}\n";
                }
            }

            // Print sink hits.
            std::cout << "\n[+] Tainted sink hits\n";
            if (interproc.sink_hits.empty()) {
                std::cout << "    (none found)\n";
            } else {
                for (const auto& hit : interproc.sink_hits) {
                    auto caller_str = method_id_string(hit.caller);
                    auto callee_str = method_id_string(hit.callee);
                    std::ostringstream args_ss;
                    for (std::size_t i = 0; i < hit.tainted_args.size(); ++i) {
                        args_ss << "arg" << hit.tainted_args[i];
                        if (i + 1 < hit.tainted_args.size()) {
                            args_ss << ",";
                        }
                    }
                    std::cout << "    " << caller_str << " ("
                              << args_ss.str() << ") -> " << callee_str
                              << " @off " << hit.offset << "\n";
                }
            }
        }

        // --- Write taint graph (independent of --quiet) ---
        if (!graph_out.empty()) {
            if (interproc.sink_hits.empty()) {
                std::cerr << "[-] No sink hits found; graph file not written.\n";
                return 1;
            }
            write_taint_graph(graph_out, interproc);
        }

        return 0;
    } catch (const std::exception& e) {
        std::cerr << "Error: " << e.what() << "\n";
        return 3;
    }
}
