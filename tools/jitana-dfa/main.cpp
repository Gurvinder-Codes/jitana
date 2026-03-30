#include <algorithm>
#include <cctype>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

#include <boost/filesystem.hpp>
#include <boost/optional.hpp>
#include <boost/system/error_code.hpp>
#include <boost/graph/graph_traits.hpp>
#include <boost/dynamic_bitset.hpp>

#include <jitana/jitana.hpp>
#include <jitana/analysis/interproc_param_taint.hpp>

using namespace jitana;
using namespace jitana::analysis::dfa;

static constexpr uint8_t APP_LOADER_ID = 100;
namespace fs = boost::filesystem;

// =============================================================================
// Utility: method ID → printable string
// =============================================================================

static std::string method_id_string(const MethodId& mid)
{
    std::ostringstream os;
    os << mid.type << "." << mid.name << mid.descriptor;
    return os.str();
}

// =============================================================================
// Channel types
// =============================================================================

enum class ChannelType { Broadcast, Activity, Service, ContentProvider };

static const char* channel_name(ChannelType ct)
{
    switch (ct) {
    case ChannelType::Broadcast:       return "Broadcast";
    case ChannelType::Activity:        return "Activity";
    case ChannelType::Service:         return "Service";
    case ChannelType::ContentProvider: return "ContentProvider";
    }
    return "Unknown";
}

static const char* channel_sender_edge_label(ChannelType ct)
{
    switch (ct) {
    case ChannelType::Broadcast:       return "sendBroadcast\\n(tainted Intent)";
    case ChannelType::Activity:        return "startActivity\\n(tainted Intent)";
    case ChannelType::Service:         return "startService\\n(tainted Intent)";
    case ChannelType::ContentProvider: return "ContentResolver\\n(tainted Uri/data)";
    }
    return "unknown";
}

static const char* channel_receiver_edge_label(ChannelType ct)
{
    switch (ct) {
    case ChannelType::Broadcast:       return "onReceive\\n(Intent tainted)";
    case ChannelType::Activity:        return "onNewIntent\\n(Intent tainted)";
    case ChannelType::Service:         return "onStartCommand\\n(Intent tainted)";
    case ChannelType::ContentProvider: return "query/insert\\n(Uri tainted)";
    }
    return "unknown";
}

static const char* channel_bridge_color(ChannelType ct)
{
    switch (ct) {
    case ChannelType::Broadcast:       return "#7d6608";
    case ChannelType::Activity:        return "#1a5e1a";
    case ChannelType::Service:         return "#5b2c6f";
    case ChannelType::ContentProvider: return "#7e5109";
    }
    return "#555555";
}

static const char* channel_bridge_fill(ChannelType ct)
{
    switch (ct) {
    case ChannelType::Broadcast:       return "#fdfde7";
    case ChannelType::Activity:        return "#eafaea";
    case ChannelType::Service:         return "#f5eafa";
    case ChannelType::ContentProvider: return "#fdf5e6";
    }
    return "#f5f5f5";
}

static const char* channel_edge_color(ChannelType ct)
{
    switch (ct) {
    case ChannelType::Broadcast:       return "#e67e22";
    case ChannelType::Activity:        return "#27ae60";
    case ChannelType::Service:         return "#8e44ad";
    case ChannelType::ContentProvider: return "#d35400";
    }
    return "#888888";
}

// =============================================================================
// APK / DEX loading helpers
// =============================================================================

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

struct DexSources {
    std::vector<std::string> files;
    boost::optional<TempDirGuard> temp_guard;
};

static fs::path make_temp_directory()
{
    auto base = fs::temp_directory_path()
            / fs::unique_path("jitana-dfa-%%%%%%%%");
    if (!fs::create_directories(base))
        throw std::runtime_error("failed to create temp directory");
    return base;
}

static void extract_apk_classes(const fs::path& apk_path,
                                const fs::path& out_dir)
{
    std::string cmd = "unzip -qq -o \"" + apk_path.string()
            + "\" \"classes*.dex\" -d \"" + out_dir.string() + "\"";
    if (std::system(cmd.c_str()) != 0)
        throw std::runtime_error("failed to extract classes*.dex from APK");
}

static DexSources prepare_dex_sources(const std::string& input_path)
{
    DexSources sources;
    fs::path in_path(input_path);
    if (!fs::exists(in_path))
        throw std::runtime_error("input path does not exist: " + input_path);

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
        for (const auto& entry : fs::directory_iterator(temp_dir)) {
            if (!entry.is_regular_file())
                continue;
            auto fname = entry.path().filename().string();
            auto dext  = entry.path().extension().string();
            std::transform(fname.begin(), fname.end(), fname.begin(),
                           [](unsigned char c) { return std::tolower(c); });
            std::transform(dext.begin(), dext.end(), dext.begin(),
                           [](unsigned char c) { return std::tolower(c); });
            if (fname.rfind("classes", 0) == 0 && dext == ".dex")
                sources.files.push_back(entry.path().string());
        }
        if (sources.files.empty())
            throw std::runtime_error("APK contained no classes*.dex files");
        std::sort(sources.files.begin(), sources.files.end());
        sources.temp_guard.emplace(temp_dir);
        return sources;
    }
    throw std::runtime_error("unsupported input type (expected .dex or .apk): "
                             + input_path);
}

static class_vertex_descriptor
ensure_placeholder_class(virtual_machine& vm, const jvm_type_hdl& type_hdl)
{
    if (auto existing = vm.find_class(type_hdl, false))
        return *existing;
    class_vertex_property prop{};
    prop.jvm_hdl      = type_hdl;
    prop.access_flags = acc_public;
    auto cv = add_vertex(prop, vm.classes());
    vm.classes()[boost::graph_bundle].jvm_hdl_to_vertex[type_hdl] = cv;
    return cv;
}

static void seed_placeholder_classes(virtual_machine& vm)
{
    static const char* kTypes[] = {
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
        // Android UI
        "Landroid/webkit/WebView;",
        // Android logging
        "Landroid/util/Log;",
        // Android SQLite
        "Landroid/database/sqlite/SQLiteDatabase;",
        // JNDI
        "Ljavax/naming/InitialContext;",
        // Android inter-app communication
        "Landroid/content/Context;",
        "Landroid/content/Intent;",
        "Landroid/content/BroadcastReceiver;",
        // Activity channel
        "Landroid/app/Activity;",
        // Service channel
        "Landroid/app/Service;",
        "Landroid/app/IntentService;",
        // Content provider channel
        "Landroid/content/ContentResolver;",
        "Landroid/content/ContentProvider;",
        "Landroid/net/Uri;",
        "Landroid/content/ContentValues;",
    };
    for (const char* desc : kTypes)
        ensure_placeholder_class(vm, {class_loader_hdl{APP_LOADER_ID}, desc});
}

static bool wire_loader(virtual_machine& vm,
                        const std::vector<std::string>& dex_files,
                        const std::string& label, bool quiet)
{
    if (dex_files.empty()) {
        std::cerr << "[-] No DEX files for: " << label << "\n";
        return false;
    }
    class_loader loader(APP_LOADER_ID, "DFALoader",
                        dex_files.begin(), dex_files.end());
    vm.add_loader(loader);
    if (!vm.load_all_classes(APP_LOADER_ID) && !quiet)
        std::cerr << "[!] Some classes from " << label
                  << " could not be loaded; continuing.\n";
    if (!quiet)
        std::cout << "[+] Loaded: " << label << "\n";
    return true;
}

// =============================================================================
// DOT graph helpers
// =============================================================================

static std::string dot_escape(const std::string& s)
{
    std::string out;
    for (char c : s) {
        if (c == '"' || c == '\\') out.push_back('\\');
        out.push_back(c);
    }
    return out;
}

static std::string html_escape(const std::string& s)
{
    std::string out;
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

static std::string type_desc_to_full_java(const std::string& desc)
{
    std::string s = desc;
    if (s.size() >= 2 && s[0] == 'L' && s.back() == ';')
        s = s.substr(1, s.size() - 2);
    for (char& c : s) if (c == '/') c = '.';
    return s;
}

static std::string type_desc_to_simple(const std::string& desc)
{
    auto full = type_desc_to_full_java(desc);
    auto dot  = full.rfind('.');
    return (dot == std::string::npos) ? full : full.substr(dot + 1);
}

static std::string type_desc_to_package(const std::string& desc)
{
    auto full = type_desc_to_full_java(desc);
    auto dot  = full.rfind('.');
    return (dot == std::string::npos) ? "" : full.substr(0, dot);
}

static std::string type_desc_to_java(const std::string& d, std::size_t pos = 0)
{
    int arrays = 0;
    while (pos < d.size() && d[pos] == '[') { ++arrays; ++pos; }
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
        auto end   = d.find(';', pos + 1);
        auto inner = (end == std::string::npos)
                         ? d.substr(pos + 1)
                         : d.substr(pos + 1, end - pos - 1);
        auto slash = inner.rfind('/');
        base = (slash == std::string::npos) ? inner : inner.substr(slash + 1);
        break;
    }
    default: base = d.substr(pos, 1);
    }
    for (int i = 0; i < arrays; ++i) base += "[]";
    return base;
}

static std::string method_desc_to_java(const std::string& desc)
{
    if (desc.empty() || desc[0] != '(') return desc;
    auto close = desc.find(')');
    if (close == std::string::npos) return desc;
    std::vector<std::string> params;
    std::size_t i = 1;
    while (i < close) {
        std::size_t start = i;
        while (i < close && desc[i] == '[') ++i;
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
    std::string ret    = type_desc_to_java(desc, close + 1);
    std::string result = "(";
    for (std::size_t k = 0; k < params.size(); ++k) {
        if (k > 0) result += ", ";
        result += params[k];
    }
    result += "): " + ret;
    return result;
}

static std::string readable_name(const std::string& name)
{
    if (name == "<init>")   return "new";
    if (name == "<clinit>") return "[static init]";
    return name;
}

static std::string node_html_label(const MethodId& mid,
                                   const std::string& hdr_bg,
                                   const std::string& hdr_fg)
{
    auto cls  = html_escape(type_desc_to_simple(mid.type.descriptor));
    auto pkg  = html_escape(type_desc_to_package(mid.type.descriptor));
    auto meth = html_escape(readable_name(mid.name)
                            + method_desc_to_java(mid.descriptor));
    std::string out;
    out += "<TABLE BORDER=\"0\" CELLBORDER=\"1\" CELLSPACING=\"0\""
           " CELLPADDING=\"5\" BGCOLOR=\"white\">";
    out += "<TR><TD BGCOLOR=\"" + hdr_bg + "\" ALIGN=\"CENTER\">"
           "<FONT COLOR=\"" + hdr_fg + "\"><B>" + cls + "</B></FONT></TD></TR>";
    if (!pkg.empty())
        out += "<TR><TD ALIGN=\"LEFT\"><FONT POINT-SIZE=\"8\""
               " COLOR=\"#666666\">" + pkg + "</FONT></TD></TR>";
    out += "<TR><TD ALIGN=\"LEFT\">" + meth + "</TD></TR>";
    out += "</TABLE>";
    return out;
}

static std::string node_tooltip(const MethodId& mid)
{
    return dot_escape(type_desc_to_full_java(mid.type.descriptor) + "."
                      + readable_name(mid.name)
                      + method_desc_to_java(mid.descriptor));
}

// =============================================================================
// Phase 1 sinks: all interapp exit points, tagged by channel
// =============================================================================

struct ChannelSink {
    ChannelType channel;
    SinkSpec    spec;
};

static const std::vector<ChannelSink> kChannelSenderSinks = {
    // Broadcast
    {ChannelType::Broadcast,
     {"Landroid/content/Context;", "sendBroadcast",
      "(Landroid/content/Intent;)V"}},
    {ChannelType::Broadcast,
     {"Landroid/content/Context;", "sendOrderedBroadcast",
      "(Landroid/content/Intent;Ljava/lang/String;)V"}},

    // Activity
    {ChannelType::Activity,
     {"Landroid/content/Context;", "startActivity",
      "(Landroid/content/Intent;)V"}},
    {ChannelType::Activity,
     {"Landroid/app/Activity;", "startActivityForResult",
      "(Landroid/content/Intent;I)V"}},

    // Service
    {ChannelType::Service,
     {"Landroid/content/Context;", "startService",
      "(Landroid/content/Intent;)Landroid/content/ComponentName;"}},
    {ChannelType::Service,
     {"Landroid/content/Context;", "bindService",
      "(Landroid/content/Intent;Landroid/content/ServiceConnection;I)Z"}},

    // ContentProvider
    {ChannelType::ContentProvider,
     {"Landroid/content/ContentResolver;", "query",
      "(Landroid/net/Uri;[Ljava/lang/String;Ljava/lang/String;"
      "[Ljava/lang/String;Ljava/lang/String;)Landroid/database/Cursor;"}},
    {ChannelType::ContentProvider,
     {"Landroid/content/ContentResolver;", "insert",
      "(Landroid/net/Uri;Landroid/content/ContentValues;)Landroid/net/Uri;"}},
    {ChannelType::ContentProvider,
     {"Landroid/content/ContentResolver;", "update",
      "(Landroid/net/Uri;Landroid/content/ContentValues;"
      "Ljava/lang/String;[Ljava/lang/String;)I"}},
    {ChannelType::ContentProvider,
     {"Landroid/content/ContentResolver;", "delete",
      "(Landroid/net/Uri;Ljava/lang/String;[Ljava/lang/String;)I"}},
};

// Flatten to a plain SinkSpec list for the analysis config.
static std::vector<SinkSpec> make_sender_sinks()
{
    std::vector<SinkSpec> v;
    for (const auto& cs : kChannelSenderSinks)
        v.push_back(cs.spec);
    return v;
}

// Determine which channel a phase-1 SinkHit belongs to.
static ChannelType classify_hit(const SinkHit& hit)
{
    for (const auto& cs : kChannelSenderSinks) {
        if (hit.callee.type.descriptor == cs.spec.type_descriptor
                && hit.callee.name == cs.spec.name)
            return cs.channel;
    }
    return ChannelType::Broadcast; // fallback
}

// Returns true if the first (non-this) argument is tainted (the Intent/Uri).
static bool first_arg_tainted(const SinkHit& hit)
{
    for (std::size_t a : hit.tainted_args)
        if (a == 0) return true;
    return false;
}

// =============================================================================
// Phase 2 sinks: dangerous downstream APIs
// =============================================================================

static const std::vector<SinkSpec> kReceiverSinks = {
    {"Landroid/util/Log;", "i",
     "(Ljava/lang/String;Ljava/lang/String;)I"},
    {"Landroid/util/Log;", "e",
     "(Ljava/lang/String;Ljava/lang/String;)I"},
    {"Landroid/util/Log;", "w",
     "(Ljava/lang/String;Ljava/lang/String;)I"},
    {"Ljava/lang/Runtime;", "exec",
     "(Ljava/lang/String;)Ljava/lang/Process;"},
    {"Ljava/io/FileOutputStream;", "<init>",
     "(Ljava/lang/String;)V"},
    {"Landroid/webkit/WebView;", "loadUrl",
     "(Ljava/lang/String;)V"},
    {"Landroid/telephony/SmsManager;", "sendTextMessage",
     "(Ljava/lang/String;Ljava/lang/String;Ljava/lang/String;"
     "Landroid/app/PendingIntent;Landroid/app/PendingIntent;)V"},
};

// =============================================================================
// Receiver entry-point discovery
// =============================================================================

// Per-channel receiver entry-point unique names (name + descriptor).
// The analysis seeds ALL parameters of matched methods as tainted.
static const std::map<ChannelType, std::vector<std::string>>
        kReceiverEntryPointSigs = {
    {ChannelType::Broadcast, {
        "onReceive(Landroid/content/Context;Landroid/content/Intent;)V",
    }},
    {ChannelType::Activity, {
        "onNewIntent(Landroid/content/Intent;)V",
    }},
    {ChannelType::Service, {
        "onStartCommand(Landroid/content/Intent;II)I",
        "onBind(Landroid/content/Intent;)Landroid/os/IBinder;",
        "onHandleIntent(Landroid/content/Intent;)V",
    }},
    {ChannelType::ContentProvider, {
        "query(Landroid/net/Uri;[Ljava/lang/String;Ljava/lang/String;"
        "[Ljava/lang/String;Ljava/lang/String;)Landroid/database/Cursor;",
        "insert(Landroid/net/Uri;Landroid/content/ContentValues;)Landroid/net/Uri;",
        "update(Landroid/net/Uri;Landroid/content/ContentValues;"
        "Ljava/lang/String;[Ljava/lang/String;)I",
        "delete(Landroid/net/Uri;Ljava/lang/String;[Ljava/lang/String;)I",
    }},
};

// Finds all methods in the VM whose unique_name matches one of the given
// signatures, optionally restricted to a specific class descriptor.
static std::vector<MethodId> find_methods_by_sig(
        const virtual_machine& vm,
        const std::vector<std::string>& sigs,
        const std::string& restrict_class = "")
{
    std::set<std::string> sig_set(sigs.begin(), sigs.end());
    std::vector<MethodId> results;
    const auto& mg = vm.methods();
    for (auto vp = vertices(mg); vp.first != vp.second; ++vp.first) {
        const auto& minfo = mg[*vp.first];
        if (sig_set.count(minfo.jvm_hdl.unique_name) == 0)
            continue;
        if (!restrict_class.empty()
                && minfo.jvm_hdl.type_hdl.descriptor != restrict_class)
            continue;
        results.push_back(make_method_id(minfo.jvm_hdl));
    }
    return results;
}

// =============================================================================
// Interapp DOT graph
// =============================================================================

struct ChannelHit {
    ChannelType channel;
    SinkHit     hit;
};

static void write_interapp_graph(
        const std::string& out_path,
        const std::vector<ChannelHit>& channel_hits,
        const InterprocParamResult& phase2)
{
    std::ofstream ofs(out_path);
    if (!ofs) {
        std::cerr << "[-] Failed to open graph output: " << out_path << "\n";
        return;
    }

    // ── Collect unique sender callers per channel ──────────────────────────
    // sender_callers: deduplicated per (channel, caller)
    std::map<ChannelType, std::vector<MethodId>> ch_sender_callers;
    std::map<ChannelType, std::map<std::string, std::size_t>> ch_sc_idx;
    for (const auto& ch : channel_hits) {
        auto key = method_id_string(ch.hit.caller);
        auto& idx = ch_sc_idx[ch.channel];
        if (idx.find(key) == idx.end()) {
            idx[key] = ch_sender_callers[ch.channel].size();
            ch_sender_callers[ch.channel].push_back(ch.hit.caller);
        }
    }

    // Which channel types have at least one hit?
    std::vector<ChannelType> active_channels;
    for (auto ct : {ChannelType::Broadcast, ChannelType::Activity,
                    ChannelType::Service,   ChannelType::ContentProvider}) {
        if (ch_sender_callers.count(ct))
            active_channels.push_back(ct);
    }

    // ── Collect unique receiver callers and sinks ──────────────────────────
    std::vector<MethodId> recv_callers, recv_sinks;
    std::map<std::string, std::size_t> rc_idx, rs_idx;
    for (const auto& hit : phase2.sink_hits) {
        {
            auto key = method_id_string(hit.caller);
            if (rc_idx.find(key) == rc_idx.end()) {
                rc_idx[key] = recv_callers.size();
                recv_callers.push_back(hit.caller);
            }
        }
        {
            auto key = method_id_string(hit.callee);
            if (rs_idx.find(key) == rs_idx.end()) {
                rs_idx[key] = recv_sinks.size();
                recv_sinks.push_back(hit.callee);
            }
        }
    }

    // ── DOT header ─────────────────────────────────────────────────────────
    ofs << "digraph InterappTaint {\n";
    ofs << "  graph [label=\"Interapp Parameter Taint\","
           " labelloc=t, fontsize=14, fontname=\"Helvetica\","
           " bgcolor=\"#fafafa\", pad=\"0.6\"];\n";
    ofs << "  rankdir=LR;\n  nodesep=0.6;\n  ranksep=2.4;\n";
    ofs << "  node [shape=none, fontname=\"Helvetica\", fontsize=10];\n";
    ofs << "  edge [fontname=\"Helvetica\", fontsize=9, penwidth=1.5];\n\n";

    // ── Sender cluster (one subgraph, nodes grouped by channel) ───────────
    ofs << "  subgraph cluster_sender {\n";
    ofs << "    label=\"Sender App\";\n";
    ofs << "    fontname=\"Helvetica\"; fontsize=12; fontcolor=\"#1a5276\";\n";
    ofs << "    style=rounded; fillcolor=\"#eaf4fb\";"
           " color=\"#2471a3\"; penwidth=2;\n";
    for (const auto ct : active_channels) {
        const auto& callers = ch_sender_callers.at(ct);
        for (std::size_t i = 0; i < callers.size(); ++i) {
            std::string nid = std::string("sc_")
                    + channel_name(ct) + "_" + std::to_string(i);
            ofs << "    " << nid << " [label=<"
                << node_html_label(callers[i], "#1a5276", "white")
                << ">, tooltip=\"" << node_tooltip(callers[i]) << "\"];\n";
        }
    }
    ofs << "  }\n\n";

    // ── Bridge nodes (one per active channel) ─────────────────────────────
    for (const auto ct : active_channels) {
        std::string nid   = std::string("bridge_") + channel_name(ct);
        std::string label = std::string(channel_name(ct)) + " Channel";
        std::string entry;
        switch (ct) {
        case ChannelType::Broadcast:
            entry = "sendBroadcast | Intent crosses\\napp boundary | onReceive";
            break;
        case ChannelType::Activity:
            entry = "startActivity | Intent crosses\\napp boundary | onNewIntent";
            break;
        case ChannelType::Service:
            entry = "startService | Intent crosses\\napp boundary | onStartCommand";
            break;
        case ChannelType::ContentProvider:
            entry = "ContentResolver | Uri/data crosses\\napp boundary | query/insert";
            break;
        }
        ofs << "  " << nid
            << " [shape=record, style=\"filled,rounded\","
            << " fillcolor=\"" << channel_bridge_fill(ct) << "\","
            << " color=\"" << channel_bridge_color(ct) << "\","
            << " fontname=\"Helvetica\", fontsize=10,"
            << " label=\"{" << entry << "}\"];\n";
    }
    ofs << "\n";

    // ── Receiver cluster ──────────────────────────────────────────────────
    ofs << "  subgraph cluster_receiver {\n";
    ofs << "    label=\"Receiver App\";\n";
    ofs << "    fontname=\"Helvetica\"; fontsize=12; fontcolor=\"#1a5276\";\n";
    ofs << "    style=rounded; fillcolor=\"#eaf4fb\";"
           " color=\"#2471a3\"; penwidth=2;\n";
    for (std::size_t i = 0; i < recv_callers.size(); ++i)
        ofs << "    rc" << i << " [label=<"
            << node_html_label(recv_callers[i], "#1a5276", "white")
            << ">, tooltip=\"" << node_tooltip(recv_callers[i]) << "\"];\n";
    ofs << "  }\n\n";

    // ── Sink cluster ──────────────────────────────────────────────────────
    ofs << "  subgraph cluster_sinks {\n";
    ofs << "    label=\"Dangerous sink APIs\";\n";
    ofs << "    fontname=\"Helvetica\"; fontsize=12; fontcolor=\"#922b21\";\n";
    ofs << "    style=rounded; fillcolor=\"#fdedec\";"
           " color=\"#922b21\"; penwidth=2;\n";
    for (std::size_t i = 0; i < recv_sinks.size(); ++i)
        ofs << "    rs" << i << " [label=<"
            << node_html_label(recv_sinks[i], "#7b241c", "white")
            << ">, tooltip=\"" << node_tooltip(recv_sinks[i]) << "\"];\n";
    ofs << "  }\n\n";

    // ── Edges: sender → bridge ────────────────────────────────────────────
    for (const auto ct : active_channels) {
        std::string bridge_nid = std::string("bridge_") + channel_name(ct);
        const auto& callers    = ch_sender_callers.at(ct);
        for (std::size_t i = 0; i < callers.size(); ++i) {
            std::string nid = std::string("sc_")
                    + channel_name(ct) + "_" + std::to_string(i);
            ofs << "  " << nid << " -> " << bridge_nid
                << " [label=\"" << channel_sender_edge_label(ct) << "\","
                << " color=\"" << channel_edge_color(ct) << "\","
                << " fontcolor=\"" << channel_bridge_color(ct) << "\","
                << " arrowhead=vee];\n";
        }
    }
    ofs << "\n";

    // ── Edges: bridge → receiver ──────────────────────────────────────────
    for (const auto ct : active_channels) {
        std::string bridge_nid = std::string("bridge_") + channel_name(ct);
        for (std::size_t i = 0; i < recv_callers.size(); ++i)
            ofs << "  " << bridge_nid << " -> rc" << i
                << " [label=\"" << channel_receiver_edge_label(ct) << "\","
                << " color=\"" << channel_edge_color(ct) << "\","
                << " fontcolor=\"" << channel_bridge_color(ct) << "\","
                << " arrowhead=vee, style=dashed];\n";
    }
    ofs << "\n";

    // ── Edges: receiver → sinks ───────────────────────────────────────────
    for (const auto& hit : phase2.sink_hits) {
        auto ci = rc_idx.at(method_id_string(hit.caller));
        auto si = rs_idx.at(method_id_string(hit.callee));
        std::ostringstream lbl;
        for (std::size_t k = 0; k < hit.tainted_args.size(); ++k) {
            if (k > 0) lbl << "\\n";
            lbl << "arg" << hit.tainted_args[k] << " tainted";
        }
        lbl << "\\n@ 0x" << std::hex << hit.offset << std::dec;
        ofs << "  rc" << ci << " -> rs" << si
            << " [label=\"" << lbl.str() << "\","
               " color=\"#e74c3c\", fontcolor=\"#922b21\","
               " arrowhead=vee];\n";
    }

    ofs << "}\n";
    ofs.close();
    std::cerr << "[+] Wrote interapp taint graph to "
              << fs::absolute(out_path).string() << "\n";
}

// =============================================================================
// main
// =============================================================================

int main(int argc, char** argv)
{
    std::string sender_path, receiver_path, receiver_class, graph_out;
    bool quiet = false;

    for (int i = 1; i < argc; ++i) {
        std::string a = argv[i];
        if      (a == "--sender"         && i + 1 < argc) sender_path    = argv[++i];
        else if (a == "--receiver"        && i + 1 < argc) receiver_path  = argv[++i];
        else if (a == "--receiver-class"  && i + 1 < argc) receiver_class = argv[++i];
        else if (a == "--taint-graph"     && i + 1 < argc) graph_out      = argv[++i];
        else if (a == "--quiet" || a == "-q")               quiet = true;
    }

    if (sender_path.empty() || receiver_path.empty()) {
        std::cerr
            << "Usage: " << argv[0]
            << " --sender <file.dex|app.apk>"
               " --receiver <file.dex|app.apk>\n"
            << "  [--receiver-class <Lcom/example/Foo;>]"
               "  restrict Phase 2 seeding to this class\n"
            << "  [--taint-graph <file.dot>]"
               "              write interapp taint graph to DOT file\n"
            << "  [--quiet|-q]"
               "                         suppress verbose output\n";
        return 2;
    }

    try {
        // ── Phase 1: sender ───────────────────────────────────────────────────
        auto sender_srcs = prepare_dex_sources(sender_path);
        virtual_machine sender_vm;
        seed_placeholder_classes(sender_vm);
        if (!wire_loader(sender_vm, sender_srcs.files, sender_path, quiet))
            return 1;

        if (!quiet)
            std::cout << "\n[Phase 1] Analyzing sender: " << sender_path
                      << " (all interapp channels)\n";

        InterprocParamConfig p1_cfg;
        p1_cfg.sinks = make_sender_sinks();
        auto phase1  = run_interproc_param_taint(sender_vm, p1_cfg);

        // Classify each hit and keep only those with a tainted first arg.
        std::vector<ChannelHit> channel_hits;
        std::map<ChannelType, std::size_t> hits_per_channel;
        for (const auto& hit : phase1.sink_hits) {
            if (!first_arg_tainted(hit))
                continue;
            ChannelType ct = classify_hit(hit);
            channel_hits.push_back({ct, hit});
            ++hits_per_channel[ct];
        }

        if (!quiet) {
            for (auto ct : {ChannelType::Broadcast, ChannelType::Activity,
                            ChannelType::Service,   ChannelType::ContentProvider}) {
                auto n = hits_per_channel.count(ct) ? hits_per_channel.at(ct) : 0u;
                if (n == 0) continue;
                std::cout << "[Phase 1] " << channel_name(ct) << ": "
                          << n << " tainted call site(s):\n";
                for (const auto& ch : channel_hits) {
                    if (ch.channel != ct) continue;
                    std::cout << "  caller : " << method_id_string(ch.hit.caller) << "\n"
                              << "  callee : " << method_id_string(ch.hit.callee)
                              << " @off 0x" << std::hex << ch.hit.offset << std::dec
                              << "\n";
                }
            }
        }

        if (channel_hits.empty()) {
            std::cout
                << "[!] No tainted interapp calls found in sender.\n"
                   "    Nothing to propagate across the app boundary.\n";
            return 0;
        }

        // ── Bridge: determine active channels and receiver seeds ──────────────
        if (!quiet)
            std::cout << "\n[Bridge] Tainted data crossing app boundary.\n";

        // ── Phase 2: receiver ─────────────────────────────────────────────────
        auto receiver_srcs = prepare_dex_sources(receiver_path);
        virtual_machine receiver_vm;
        seed_placeholder_classes(receiver_vm);
        if (!wire_loader(receiver_vm, receiver_srcs.files, receiver_path, quiet))
            return 1;

        // Collect seeds for every active channel.
        std::vector<MethodId> all_seeds;
        for (auto ct : {ChannelType::Broadcast, ChannelType::Activity,
                        ChannelType::Service,   ChannelType::ContentProvider}) {
            if (!hits_per_channel.count(ct))
                continue;
            const auto& sigs = kReceiverEntryPointSigs.at(ct);
            auto seeds = find_methods_by_sig(receiver_vm, sigs, receiver_class);
            if (!quiet) {
                std::cout << "[Bridge] " << channel_name(ct)
                          << ": seeding " << seeds.size()
                          << " receiver entry point(s)";
                if (!receiver_class.empty())
                    std::cout << " (class=" << receiver_class << ")";
                std::cout << ":\n";
                for (const auto& mid : seeds)
                    std::cout << "  " << method_id_string(mid) << "\n";
            }
            all_seeds.insert(all_seeds.end(), seeds.begin(), seeds.end());
        }

        if (all_seeds.empty()) {
            std::cout << "[!] No receiver entry points found in receiver APK.\n";
            return 0;
        }

        if (!quiet)
            std::cout << "\n[Phase 2] Analyzing receiver: " << receiver_path
                      << "\n";

        InterprocParamConfig p2_cfg;
        p2_cfg.sinks          = kReceiverSinks;
        p2_cfg.source_methods = all_seeds;
        auto phase2           = run_interproc_param_taint(receiver_vm, p2_cfg);

        // ── Report ────────────────────────────────────────────────────────────
        if (!quiet) {
            std::cout << "\n[Phase 2] Receiver sink hits: "
                      << phase2.sink_hits.size() << "\n";
            if (phase2.sink_hits.empty()) {
                std::cout << "  (none)\n";
            } else {
                for (const auto& hit : phase2.sink_hits) {
                    std::ostringstream args;
                    for (std::size_t k = 0; k < hit.tainted_args.size(); ++k) {
                        if (k) args << ", ";
                        args << "arg" << hit.tainted_args[k];
                    }
                    std::cout
                        << "  caller : " << method_id_string(hit.caller) << "\n"
                        << "  callee : " << method_id_string(hit.callee)
                        << " (" << args.str() << ")"
                        << " @off 0x" << std::hex << hit.offset << std::dec
                        << "\n";
                }
            }
        }

        // ── Summary (always printed) ──────────────────────────────────────────
        std::cout << "\n[Summary]\n";
        for (auto ct : {ChannelType::Broadcast, ChannelType::Activity,
                        ChannelType::Service,   ChannelType::ContentProvider}) {
            auto n = hits_per_channel.count(ct) ? hits_per_channel.at(ct) : 0u;
            if (n)
                std::cout << "  " << channel_name(ct)
                          << " tainted calls  : " << n << "\n";
        }
        std::cout << "  Receiver sink hits        : "
                  << phase2.sink_hits.size() << "\n";
        if (!phase2.sink_hits.empty())
            std::cout << "  *** Interapp taint path found! ***\n";

        // ── DOT graph ─────────────────────────────────────────────────────────
        if (!graph_out.empty()) {
            if (channel_hits.empty() && phase2.sink_hits.empty()) {
                std::cerr << "[-] Nothing to graph.\n";
            } else {
                write_interapp_graph(graph_out, channel_hits, phase2);
            }
        }

        return 0;
    }
    catch (const std::exception& e) {
        std::cerr << "Error: " << e.what() << "\n";
        return 3;
    }
}
