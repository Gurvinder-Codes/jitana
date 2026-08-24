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
#include <jitana/analysis/intent_flow.hpp>
#include <jitana/algorithm/property_tree.hpp>

using namespace jitana;

static constexpr uint8_t BOOTSTRAP_LOADER_ID = 0;
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
                        const std::string& label, bool quiet,
                        uint8_t loader_id,
                        const std::string& apk_dir = "") {
    if (dex_files.empty()) {
        std::cerr << "[-] No DEX files provided to wire loader.\n";
        return false;
    }
    class_loader loader(loader_id, "DFALoader", dex_files.begin(),
                        dex_files.end());
    // Use bootstrap loader as parent so class lookup can resolve framework
    // stubs (BroadcastReceiver, Activity, etc.) when loading app classes.
    vm.add_loader(loader, class_loader_hdl{BOOTSTRAP_LOADER_ID});

    // Populate the class graph (available on most Jitana trees).
    if (!vm.load_all_classes(loader_id)) {
        // Suppress warning when quiet - this is just informational
        if (!quiet) {
            std::cerr << "[!] Some classes could not be loaded from " << label
                      << " (likely missing dependencies); continuing with those "
                         "that succeeded.\n";
        }
    }

    // Attach apk_info so manifest-based intent routing can work.
    if (!apk_dir.empty()) {
        if (auto lv = find_loader_vertex(class_loader_hdl{loader_id},
                                         vm.loaders())) {
            try {
                vm.loaders()[*lv].info = apk_info(apk_dir);
            }
            catch (...) {
                // Manifest not available or unparseable — skip silently.
            }
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
        "Ljava/lang/Thread;",
        "Ljava/lang/Runnable;",
        "Landroid/os/AsyncTask;",
        // Java reflection
        "Ljava/lang/reflect/Method;",
        "Ljava/lang/reflect/Field;",
        "Ljava/lang/reflect/Constructor;",
        "Ljava/lang/reflect/AccessibleObject;",
        // Java I/O
        "Ljava/io/PrintStream;",
        "Ljava/io/OutputStream;",
        "Ljava/io/FileOutputStream;",
        "Ljava/io/FilterOutputStream;",
        "Ljava/io/DataOutputStream;",
        "Ljava/io/BufferedOutputStream;",
        "Ljava/io/InputStream;",
        "Ljava/io/FileInputStream;",
        "Ljava/io/FilterInputStream;",
        "Ljava/io/DataInputStream;",
        "Ljava/io/BufferedInputStream;",
        "Ljava/io/Writer;",
        "Ljava/io/OutputStreamWriter;",
        "Ljava/io/FileWriter;",
        "Ljava/io/BufferedWriter;",
        "Ljava/io/PrintWriter;",
        "Ljava/io/Reader;",
        "Ljava/io/InputStreamReader;",
        "Ljava/io/BufferedReader;",
        "Ljava/io/RandomAccessFile;",
        // Java networking
        "Ljava/net/URL;",
        "Ljava/net/Socket;",
        "Ljava/net/URLConnection;",
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
        // SQLiteOpenHelper — extremely common base class for custom DB
        // helpers (class MyDbHelper extends SQLiteOpenHelper). Missing
        // this meant any such subclass's superclass failed to resolve,
        // silently failing to load the ENTIRE class (dex_file::load_class
        // returns boost::none if any superclass/interface is unresolved) —
        // confirmed via TaintBench's save_me.apk, where
        // DatabaseOperationslogin (extends SQLiteOpenHelper) never
        // appeared in any output at all.
        "Landroid/database/sqlite/SQLiteOpenHelper;",
        // JNDI
        "Ljavax/naming/InitialContext;",
        // Android inter-app communication
        "Landroid/content/Context;",
        "Landroid/content/ContextWrapper;",
        "Landroid/content/Intent;",
        "Landroid/app/Activity;",
        "Landroid/app/Service;",
        "Landroid/app/IntentService;",
        "Landroid/app/Application;",
        "Landroid/app/Fragment;",
        "Landroid/support/v4/app/Fragment;",
        "Landroid/content/BroadcastReceiver;",
        "Landroid/content/ContentProvider;",
        "Landroid/content/ContentResolver;",
        "Landroid/content/ContentValues;",
        "Landroid/net/Uri;",
        "Landroid/os/Bundle;",
        "Landroid/os/IBinder;",
        // Android UI — needed so View.OnClickListener implementors load
        "Landroid/view/View;",
        "Landroid/view/View$OnClickListener;",
        "Landroid/widget/Button;",
        "Landroid/widget/TextView;",
        "Landroid/widget/EditText;",
        // Android location — source APIs and callback interfaces
        "Landroid/location/Location;",
        "Landroid/location/LocationManager;",
        "Landroid/location/LocationListener;",
        // Android global callback interfaces (RegisterGlobal patterns)
        "Landroid/app/Application$ActivityLifecycleCallbacks;",
        "Landroid/content/ComponentCallbacks2;",
        "Landroid/content/res/Configuration;",
        // Android SharedPreferences — interface needed so classes that implement
        // OnSharedPreferenceChangeListener load successfully (dex_file.cpp
        // returns boost::none if any directly-listed interface is missing).
        "Landroid/content/SharedPreferences;",
        "Landroid/content/SharedPreferences$OnSharedPreferenceChangeListener;",
        "Landroid/content/SharedPreferences$Editor;",
    };

    for (const char* desc : kBootstrapTypes) {
        ensure_placeholder_class(vm, {class_loader_hdl{BOOTSTRAP_LOADER_ID}, desc});
    }

    // Placeholder classes above have no bytecode of their own, so unlike app
    // classes (wired up by dex_file::load_class from real class_def_item
    // superclass_idx values) they get no class_super_edge_property links.
    // Sink/source subtype matching (collect_supertype_descriptors) walks
    // those edges, so without them a call statically typed as e.g.
    // OutputStreamWriter.write(...) or HttpURLConnection.getOutputStream()
    // never matches the generic Writer.write(...) / URLConnection sink
    // specs. Wire up the real java.io / java.net hierarchy here so subtype
    // matching works for framework stream/connection wrapper types.
    auto link = [&](const char* sub_desc, const char* super_desc) {
        auto sub_v = ensure_placeholder_class(
                vm, {class_loader_hdl{BOOTSTRAP_LOADER_ID}, sub_desc});
        auto super_v = ensure_placeholder_class(
                vm, {class_loader_hdl{BOOTSTRAP_LOADER_ID}, super_desc});
        add_edge(super_v, sub_v, class_super_edge_property{false},
                 vm.classes());
    };

    link("Ljava/io/FileOutputStream;", "Ljava/io/OutputStream;");
    link("Ljava/io/FilterOutputStream;", "Ljava/io/OutputStream;");
    link("Ljava/io/DataOutputStream;", "Ljava/io/FilterOutputStream;");
    link("Ljava/io/BufferedOutputStream;", "Ljava/io/FilterOutputStream;");

    link("Ljava/io/FileInputStream;", "Ljava/io/InputStream;");
    link("Ljava/io/FilterInputStream;", "Ljava/io/InputStream;");
    link("Ljava/io/DataInputStream;", "Ljava/io/FilterInputStream;");
    link("Ljava/io/BufferedInputStream;", "Ljava/io/FilterInputStream;");

    link("Ljava/io/OutputStreamWriter;", "Ljava/io/Writer;");
    link("Ljava/io/FileWriter;", "Ljava/io/OutputStreamWriter;");
    link("Ljava/io/BufferedWriter;", "Ljava/io/Writer;");
    link("Ljava/io/PrintWriter;", "Ljava/io/Writer;");

    link("Ljava/io/InputStreamReader;", "Ljava/io/Reader;");
    link("Ljava/io/BufferedReader;", "Ljava/io/Reader;");

    link("Ljava/net/HttpURLConnection;", "Ljava/net/URLConnection;");
}

struct DexSources {
    std::vector<std::string> files;
    std::string apk_dir; // Extracted APK dir with AndroidManifest.xml; empty for .dex.
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
    // Extract DEX files (required).
    std::string cmd = "unzip -qq -o \"" + apk_path.string()
            + "\" \"classes*.dex\" -d \"" + out_dir.string() + "\"";
    if (std::system(cmd.c_str()) != 0) {
        throw std::runtime_error("failed to extract classes*.dex from APK");
    }
    // Extract AndroidManifest.xml for intent routing (optional).
    std::string mcmd = "unzip -qq -o \"" + apk_path.string()
            + "\" \"AndroidManifest.xml\" -d \"" + out_dir.string()
            + "\" 2>/dev/null";
    std::system(mcmd.c_str()); // ignore failure — manifest may be absent
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
        sources.apk_dir = temp_dir.string();
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
//  │  MyApp.apk                   │  ← APK filename (when known)
//  ├──────────────────────────────┤
//  │  com.example.package         │  ← small grey package row
//  ├──────────────────────────────┤
//  │  methodName(Type, …): Ret    │  ← method signature
//  └──────────────────────────────┘
static std::string node_html_label(const analysis::dfa::MethodId& mid,
                                   const std::string& hdr_bg,
                                   const std::string& hdr_fg,
                                   const std::string& apk_name = "")
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
    if (!apk_name.empty()) {
        out += "<TR><TD ALIGN=\"CENTER\">"
               "<FONT POINT-SIZE=\"8\" COLOR=\"#2e4057\"><I>"
               + html_escape(apk_name)
               + "</I></FONT></TD></TR>";
    }
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

// Returns true for sinks that represent inter-app IPC channels
// (Intent dispatch, ContentResolver, etc.) so they can be coloured
// differently from other dangerous sinks in the DOT graph.
static bool is_interapp_sink(const std::string& type_desc)
{
    static const char* kInterappTypes[] = {
        "Landroid/content/Intent;",
        "Landroid/content/Context;",
        "Landroid/app/Activity;",
        "Landroid/content/ContentResolver;",
    };
    for (const char* t : kInterappTypes) {
        if (type_desc == t) return true;
    }
    return false;
}

// Returns a human-readable origin label for a sink's type descriptor,
// used in place of an APK name for framework/SDK sink nodes.
static std::string sink_origin_label(const std::string& type_desc)
{
    if (type_desc.rfind("Landroid/", 0) == 0
        || type_desc.rfind("Lcom/android/", 0) == 0
        || type_desc.rfind("Ldalvik/", 0) == 0) {
        return "Android Framework";
    }
    if (type_desc.rfind("Ljava/", 0) == 0
        || type_desc.rfind("Ljavax/", 0) == 0
        || type_desc.rfind("Lsun/", 0) == 0) {
        return "Java SDK";
    }
    return "Framework";
}

// ---------------------------------------------------------------------------
// Inter-app chain: sender IPC call → receiver entry point → downstream sinks.

struct InterAppChain {
    analysis::dfa::SinkHit sender_hit;    // IPC dispatch in sender APK
    analysis::dfa::MethodId receiver_entry; // Entry point in receiver APK
    std::string receiver_apk_name;          // Filename of receiver APK
    std::vector<analysis::dfa::SinkHit> receiver_sink_hits; // Downstream sinks
};

static bool is_ipc_dispatch(const std::string& name)
{
    return name == "sendBroadcast" || name == "sendOrderedBroadcast"
        || name == "sendStickyBroadcast" || name == "startActivity"
        || name == "startActivityForResult" || name == "startService"
        || name == "startForegroundService" || name == "bindService"
        || name == "setResult";
}

// Compute cross-app taint chains by routing each IPC dispatch sink hit to
// receiver entry points.  Two strategies are used in order:
//   1. Manifest-based: parse AndroidManifest.xml from each APK to resolve
//      explicit / implicit intent targets (requires apk_info on loaders).
//   2. Structural fallback: when no manifest data is available, connect every
//      IPC dispatch in each loader to all receiver entry-point methods found
//      in any OTHER loader.  This is permissive but correct for stripped APKs
//      that contain only a classes.dex file.
static std::vector<InterAppChain> compute_ipc_chains(
        virtual_machine& vm,
        const analysis::dfa::InterprocParamResult& result,
        const std::unordered_map<uint8_t, std::string>& loader_names)
{
    const auto& mg = vm.methods();
    const auto& lg = vm.loaders();

    // Receiver entry point signatures, keyed by IPC dispatch method name.
    struct EP { std::string name; std::string desc; };
    auto get_eps = [](const std::string& sink) -> std::vector<EP> {
        if (sink == "sendBroadcast" || sink == "sendOrderedBroadcast"
            || sink == "sendStickyBroadcast")
            return {{"onReceive",
                     "(Landroid/content/Context;Landroid/content/Intent;)V"}};
        if (sink == "startActivity")
            return {{"onCreate", "(Landroid/os/Bundle;)V"}};
        if (sink == "startActivityForResult")
            // Models both direct launch (onCreate) and the return path via
            // setResult → onActivityResult.
            return {{"onCreate",          "(Landroid/os/Bundle;)V"},
                    {"onActivityResult",  "(IILandroid/content/Intent;)V"}};
        if (sink == "setResult")
            // setResult(int, Intent) is the sender side of the return path;
            // the caller's onActivityResult receives the result Intent.
            return {{"onActivityResult",  "(IILandroid/content/Intent;)V"}};
        if (sink == "startService" || sink == "startForegroundService"
            || sink == "bindService")
            return {{"onStartCommand", "(Landroid/content/Intent;II)I"},
                    {"onBind",
                     "(Landroid/content/Intent;)Landroid/os/IBinder;"}};
        return {};
    };

    // Collect all loader IDs that have actual app code (non-zero vertex count
    // excluding the placeholder loader).
    std::set<uint8_t> app_loader_ids;
    for (auto mvp = vertices(mg); mvp.first != mvp.second; ++mvp.first) {
        uint8_t lid = mg[*mvp.first].hdl.file_hdl.loader_hdl.idx;
        app_loader_ids.insert(lid);
    }

    // Strategy 1: manifest-based routing.
    auto explicit_hdls = detail::compute_explicit_intent_handlers(vm);
    auto implicit_hdls = detail::compute_implicit_intent_handlers(vm);
    const bool have_manifest = !explicit_hdls.empty() || !implicit_hdls.empty();

    // sender_loader_id → set of target loader IDs.
    std::unordered_map<uint8_t, std::set<uint8_t>> sender_to_target_lids;

    if (have_manifest) {
        // Build target sets from manifest handler maps using const-string scan.
        for (auto mvp = vertices(mg); mvp.first != mvp.second; ++mvp.first) {
            const auto& m = mg[*mvp.first];
            uint8_t lid = m.hdl.file_hdl.loader_hdl.idx;
            for (const auto& iv :
                 boost::make_iterator_range(vertices(m.insns))) {
                const auto* cs =
                        get<insn_const_string>(&m.insns[iv].insn);
                if (!cs) continue;
                auto eit = explicit_hdls.find(cs->const_val);
                if (eit != explicit_hdls.end()) {
                    for (auto lv : eit->second) {
                        uint8_t tlid = lg[lv].loader.hdl().idx;
                        sender_to_target_lids[lid].insert(tlid);
                    }
                }
                auto iit = implicit_hdls.find(cs->const_val);
                if (iit != implicit_hdls.end()) {
                    for (auto lv : iit->second) {
                        uint8_t tlid = lg[lv].loader.hdl().idx;
                        sender_to_target_lids[lid].insert(tlid);
                    }
                }
            }
        }
    }
    // Structural fallback: for any loader that manifest routing did NOT connect
    // to any target (e.g. implicit intents with action/MIME type only), connect
    // it to all other app loaders.  This supplements manifest routing rather
    // than replacing it, so explicit connections are preserved.
    for (uint8_t lid : app_loader_ids) {
        if (sender_to_target_lids.find(lid) == sender_to_target_lids.end()) {
            for (uint8_t other : app_loader_ids) {
                if (other != lid)
                    sender_to_target_lids[lid].insert(other);
            }
        }
    }

    std::vector<InterAppChain> chains;
    std::set<std::pair<std::string, std::string>> seen;

    // Helper: build a chain for one IPC dispatch identified by caller, offset,
    // and callee name.  Used for both SinkHit and SourceHit IPC dispatches.
    auto add_ipc_chains = [&](const analysis::dfa::MethodId& caller,
                               uint32_t /*offset*/,
                               const std::string& dispatch_name,
                               analysis::dfa::SinkHit ipc_hit) {
        uint8_t sender_lid = caller.type.loader_hdl.idx;

        auto tit = sender_to_target_lids.find(sender_lid);
        if (tit == sender_to_target_lids.end()) return;

        auto eps = get_eps(dispatch_name);
        if (eps.empty()) return;

        for (uint8_t target_lid : tit->second) {
            if (target_lid == sender_lid) continue; // skip intra-app

            for (auto mvp = vertices(mg);
                 mvp.first != mvp.second; ++mvp.first) {
                const auto& m = mg[*mvp.first];
                if (m.hdl.file_hdl.loader_hdl.idx != target_lid) continue;

                for (const auto& ep : eps) {
                    if (m.jvm_hdl.unique_name != ep.name + ep.desc) continue;

                    auto entry_mid =
                            analysis::dfa::make_method_id(m.jvm_hdl);

                    auto dedup_key = std::make_pair(
                            caller.type.descriptor + "." + caller.name
                                    + "@" + dispatch_name,
                            m.jvm_hdl.type_hdl.descriptor + "."
                                    + m.jvm_hdl.unique_name);
                    if (seen.count(dedup_key)) continue;
                    seen.insert(dedup_key);

                    std::vector<analysis::dfa::SinkHit> rec_hits;
                    for (const auto& rh : result.sink_hits) {
                        if (rh.caller.type.loader_hdl.idx == target_lid
                            && !is_ipc_dispatch(rh.callee.name))
                            rec_hits.push_back(rh);
                    }

                    std::string rec_apk;
                    auto nit = loader_names.find(target_lid);
                    if (nit != loader_names.end())
                        rec_apk = fs::path(nit->second).filename().string();

                    chains.push_back({ipc_hit, entry_mid, rec_apk,
                                      std::move(rec_hits)});
                }
            }
        }
    };

    // Route param-taint IPC dispatch sink hits.
    for (const auto& hit : result.sink_hits) {
        if (!is_ipc_dispatch(hit.callee.name)) continue;
        add_ipc_chains(hit.caller, hit.offset, hit.callee.name, hit);
    }

    // Also route source-to-sink IPC dispatch hits (e.g. startActivityForResult
    // whose Intent carries source-tainted data placed via putExtra).
    for (const auto& hit : result.source_sink_hits) {
        if (!is_ipc_dispatch(hit.sink_callee.name)) continue;
        // Build a synthetic SinkHit so we can reuse the same chain structure.
        analysis::dfa::SinkHit ipc_hit;
        ipc_hit.caller = hit.caller;
        ipc_hit.offset = hit.sink_offset;
        ipc_hit.callee = hit.sink_callee;
        ipc_hit.tainted_args = hit.tainted_args;
        add_ipc_chains(hit.caller, hit.sink_offset, hit.sink_callee.name,
                       ipc_hit);
    }

    return chains;
}

// ---------------------------------------------------------------------------
// Edge-label helper: build "argN (Type) tainted\n@ 0xOFF" string.

static std::string make_edge_label(const std::set<int>& tainted_args,
                                   const std::vector<uint32_t>& offsets,
                                   const std::string& callee_desc)
{
    auto param_types = get_param_types(callee_desc);
    std::ostringstream out;
    bool first = true;
    for (int a : tainted_args) {
        if (!first) out << "\\n";
        first = false;
        std::string hint;
        if (a == 0) {
            hint = " (this)";
        } else {
            auto idx = static_cast<std::size_t>(a - 1);
            if (idx < param_types.size())
                hint = " (" + param_types[idx] + ")";
        }
        out << "arg" << a << hint << " tainted";
    }
    if (offsets.size() == 1) {
        out << "\\n@ 0x" << std::hex << offsets[0] << std::dec;
    } else {
        out << "\\n" << offsets.size() << " call sites";
    }
    return out.str();
}

// ---------------------------------------------------------------------------

static void write_taint_graph(
        const std::string& graph_out,
        const analysis::dfa::InterprocParamResult& interproc,
        const std::unordered_map<uint8_t, std::string>& loader_names,
        const std::vector<InterAppChain>& chains)
{
    std::ofstream ofs(graph_out);
    if (!ofs) {
        std::cerr << "[-] Failed to open graph output file: " << graph_out
                  << "\n";
        return;
    }

    // Helper: look up the APK filename for a given MethodId.
    auto apk_label = [&](const analysis::dfa::MethodId& mid) -> std::string {
        auto it = loader_names.find(mid.type.loader_hdl.idx);
        if (it != loader_names.end())
            return fs::path(it->second).filename().string();
        return "";
    };

    // -----------------------------------------------------------------------
    // 4-LEVEL LAYOUT (when inter-app chains exist):
    //   Level 1 (blue)   – Sender methods in the originating APK
    //   Level 2 (orange) – IPC / inter-app APIs called by the sender
    //   Level 3 (green)  – Receiver entry points in the target APK
    //   Level 4 (red)    – Dangerous sink APIs reached from the receiver
    // -----------------------------------------------------------------------
    if (!chains.empty()) {
        // ---- Collect unique nodes for each level --------------------------
        using MID = analysis::dfa::MethodId;
        using MIDHash = analysis::dfa::MethodIdHash;

        std::vector<MID> senders, ipc_apis, receivers, danger_sinks;
        std::unordered_map<MID, std::size_t, MIDHash>
                sender_idx, ipc_idx, recv_idx, danger_idx;

        auto get_or_add = [](std::vector<MID>& list,
                             std::unordered_map<MID, std::size_t, MIDHash>& idx,
                             const MID& mid) -> std::size_t {
            auto it = idx.find(mid);
            if (it != idx.end()) return it->second;
            std::size_t i = list.size();
            idx[mid] = i;
            list.push_back(mid);
            return i;
        };

        // Merged edges: (from_idx, to_idx) → {tainted_args, offsets}
        struct MEdge { std::set<int> args; std::vector<uint32_t> offs; };
        std::map<std::pair<std::size_t,std::size_t>, MEdge> se_edges; // sender→IPC
        std::set<std::pair<std::size_t,std::size_t>> ipc_recv_edges;  // IPC→receiver
        std::map<std::pair<std::size_t,std::size_t>, MEdge> rd_edges; // receiver→danger

        // Populate levels from chains.
        for (const auto& chain : chains) {
            std::size_t si = get_or_add(senders, sender_idx, chain.sender_hit.caller);
            std::size_t ii = get_or_add(ipc_apis, ipc_idx,  chain.sender_hit.callee);

            auto& se = se_edges[{si, ii}];
            for (std::size_t a : chain.sender_hit.tainted_args)
                se.args.insert(static_cast<int>(a));
            se.offs.push_back(chain.sender_hit.offset);

            if (is_ipc_dispatch(chain.sender_hit.callee.name)) {
                std::size_t ri = get_or_add(receivers, recv_idx, chain.receiver_entry);
                ipc_recv_edges.insert({ii, ri});

                for (const auto& rh : chain.receiver_sink_hits) {
                    std::size_t di = get_or_add(danger_sinks, danger_idx, rh.callee);
                    auto& re = rd_edges[{ri, di}];
                    for (std::size_t a : rh.tainted_args)
                        re.args.insert(static_cast<int>(a));
                    re.offs.push_back(rh.offset);
                }
            }
        }

        // Also add other IPC sink hits from sender methods (e.g. putExtra)
        // that aren't stored in chain.sender_hit (which holds only the
        // dispatch call).
        for (const auto& hit : interproc.sink_hits) {
            if (!is_interapp_sink(hit.callee.type.descriptor)) continue;
            auto sit = sender_idx.find(hit.caller);
            if (sit == sender_idx.end()) continue;
            std::size_t si = sit->second;
            std::size_t ii = get_or_add(ipc_apis, ipc_idx, hit.callee);
            auto& se = se_edges[{si, ii}];
            for (std::size_t a : hit.tainted_args)
                se.args.insert(static_cast<int>(a));
            se.offs.push_back(hit.offset);
        }

        // ---- Write DOT -------------------------------------------------------
        ofs << "digraph TaintGraph {\n";
        ofs << "  graph [label=\"Inter-App Parameter Taint Flow\\n"
               "Tainted parameters propagate from sender APK through IPC "
               "boundary to receiver APK\","
               " labelloc=t, fontsize=14, fontname=\"Helvetica\","
               " bgcolor=\"#fafafa\", pad=\"0.6\", newrank=true];\n";
        ofs << "  rankdir=LR;\n";
        ofs << "  nodesep=0.7;\n";
        ofs << "  ranksep=2.0;\n";
        ofs << "  node [shape=none, fontname=\"Helvetica\", fontsize=10];\n";
        ofs << "  edge [fontname=\"Helvetica\", fontsize=9, penwidth=1.5];\n\n";

        // -- Level 1: Sender methods ------------------------------------------
        ofs << "  subgraph cluster_senders {\n";
        ofs << "    label=\"Level 1 — Sender Methods\";\n";
        ofs << "    fontname=\"Helvetica\"; fontsize=12; fontcolor=\"#1a5276\";\n";
        ofs << "    style=rounded; fillcolor=\"#eaf4fb\";"
               " color=\"#2471a3\"; penwidth=2;\n";
        for (std::size_t i = 0; i < senders.size(); ++i) {
            const auto& mid = senders[i];
            ofs << "    S" << i << " [label=<"
                << node_html_label(mid, "#1a5276", "white", apk_label(mid))
                << ">, tooltip=\"" << node_tooltip(mid) << "\"];\n";
        }
        ofs << "  }\n\n";

        // -- Level 2: IPC / inter-app APIs ------------------------------------
        ofs << "  subgraph cluster_ipc {\n";
        ofs << "    label=\"Level 2 — IPC / Inter-App APIs\";\n";
        ofs << "    fontname=\"Helvetica\"; fontsize=12; fontcolor=\"#784212\";\n";
        ofs << "    style=rounded; fillcolor=\"#fef5e7\";"
               " color=\"#d35400\"; penwidth=2;\n";
        for (std::size_t i = 0; i < ipc_apis.size(); ++i) {
            const auto& mid = ipc_apis[i];
            ofs << "    I" << i << " [label=<"
                << node_html_label(mid, "#d35400", "white",
                                   sink_origin_label(mid.type.descriptor))
                << ">, tooltip=\"" << node_tooltip(mid) << "\"];\n";
        }
        ofs << "  }\n\n";

        // -- Level 3: Receiver entry points -----------------------------------
        ofs << "  subgraph cluster_receivers {\n";
        ofs << "    label=\"Level 3 — Receiver Entry Points\";\n";
        ofs << "    fontname=\"Helvetica\"; fontsize=12; fontcolor=\"#1e8449\";\n";
        ofs << "    style=rounded; fillcolor=\"#eafaf1\";"
               " color=\"#1e8449\"; penwidth=2;\n";
        for (std::size_t i = 0; i < receivers.size(); ++i) {
            const auto& mid = receivers[i];
            std::string rec_apk;
            for (const auto& ch : chains) {
                if (ch.receiver_entry == mid) { rec_apk = ch.receiver_apk_name; break; }
            }
            ofs << "    R" << i << " [label=<"
                << node_html_label(mid, "#1e8449", "white", rec_apk)
                << ">, tooltip=\"" << node_tooltip(mid) << "\"];\n";
        }
        ofs << "  }\n\n";

        // -- Level 4: Dangerous sinks -----------------------------------------
        ofs << "  subgraph cluster_danger {\n";
        ofs << "    label=\"Level 4 — Dangerous Sink APIs\";\n";
        ofs << "    fontname=\"Helvetica\"; fontsize=12; fontcolor=\"#922b21\";\n";
        ofs << "    style=rounded; fillcolor=\"#fdedec\";"
               " color=\"#922b21\"; penwidth=2;\n";
        for (std::size_t i = 0; i < danger_sinks.size(); ++i) {
            const auto& mid = danger_sinks[i];
            ofs << "    D" << i << " [label=<"
                << node_html_label(mid, "#7b241c", "white",
                                   sink_origin_label(mid.type.descriptor))
                << ">, tooltip=\"" << node_tooltip(mid) << "\"];\n";
        }
        ofs << "  }\n\n";

        // Enforce 4-column ordering: each level shares the same rank.
        // newrank=true (set on the graph) allows these to work across clusters.
        ofs << "  { rank=same;";
        for (std::size_t i = 0; i < senders.size(); ++i)   ofs << " S" << i << ";";
        ofs << " }\n";
        ofs << "  { rank=same;";
        for (std::size_t i = 0; i < ipc_apis.size(); ++i)  ofs << " I" << i << ";";
        ofs << " }\n";
        ofs << "  { rank=same;";
        for (std::size_t i = 0; i < receivers.size(); ++i) ofs << " R" << i << ";";
        ofs << " }\n";
        ofs << "  { rank=same;";
        for (std::size_t i = 0; i < danger_sinks.size(); ++i) ofs << " D" << i << ";";
        ofs << " }\n\n";

        // -- Edges: Level 1 → Level 2 -----------------------------------------
        for (const auto& kv : se_edges) {
            std::size_t si = kv.first.first, ii = kv.first.second;
            auto lbl = make_edge_label(kv.second.args, kv.second.offs,
                                       ipc_apis[ii].descriptor);
            ofs << "  S" << si << " -> I" << ii
                << " [label=\"" << lbl << "\","
                   " color=\"#e67e22\", fontcolor=\"#d35400\","
                   " arrowhead=vee];\n";
        }

        // -- Edges: Level 2 → Level 3 (dashed IPC boundary) ------------------
        for (const auto& p : ipc_recv_edges) {
            ofs << "  I" << p.first << " -> R" << p.second
                << " [style=dashed, color=\"#1e8449\", fontcolor=\"#1e8449\","
                   " label=\"IPC boundary\", arrowhead=open, penwidth=2];\n";
        }

        // -- Edges: Level 3 → Level 4 -----------------------------------------
        for (const auto& kv : rd_edges) {
            std::size_t ri = kv.first.first, di = kv.first.second;
            auto lbl = make_edge_label(kv.second.args, kv.second.offs,
                                       danger_sinks[di].descriptor);
            ofs << "  R" << ri << " -> D" << di
                << " [label=\"" << lbl << "\","
                   " color=\"#e74c3c\", fontcolor=\"#922b21\","
                   " arrowhead=vee];\n";
        }

        // -- Legend -----------------------------------------------------------
        ofs << "\n  subgraph cluster_legend {\n";
        ofs << "    label=\"Legend\"; style=rounded; fontsize=9;\n";
        ofs << "    fontname=\"Helvetica\"; color=\"#aaaaaa\"; fillcolor=\"#f5f5f5\";\n";
        ofs << "    node [shape=plaintext, fontsize=9, fontname=\"Helvetica\"];\n";
        ofs << "    leg [label=\""
               "Level 1 (Blue)   — Sender method in originating APK\\n"
               "Level 2 (Orange) — IPC / inter-app API (putExtra, sendBroadcast, ...)\\n"
               "Level 3 (Green)  — Receiver entry point in target APK\\n"
               "Level 4 (Red)    — Dangerous sink API reached from receiver\\n"
               "Dashed arrow     — IPC boundary (data crosses app boundary)\\n"
               "Solid arrow      — Tainted argument flowing between levels\\n"
               "  arg 0 = this (virtual calls), arg 1 = first param, ...\"];\n";
        ofs << "  }\n";
        ofs << "}\n";

    } else {
        // -----------------------------------------------------------------------
        // FALLBACK 2-LEVEL LAYOUT (no inter-app chains detected):
        //   Callers → Sinks
        // -----------------------------------------------------------------------
        std::vector<analysis::dfa::MethodId> caller_list, sink_list;
        std::unordered_map<analysis::dfa::MethodId, std::size_t,
                           analysis::dfa::MethodIdHash>
                caller_idx, sink_idx;

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
            me.ci = ci; me.si = si;
            for (std::size_t a : hit.tainted_args)
                me.tainted_args.insert(static_cast<int>(a));
            me.offsets.push_back(hit.offset);
        }

        ofs << "digraph TaintGraph {\n";
        ofs << "  graph [label=\"Parameter Taint Analysis\\n"
               "Tainted method parameters flow from app methods to dangerous"
               " sink APIs\","
               " labelloc=t, fontsize=14, fontname=\"Helvetica\","
               " bgcolor=\"#fafafa\", pad=\"0.5\"];\n";
        ofs << "  rankdir=TB;\n  nodesep=0.8;\n  ranksep=1.4;\n";
        ofs << "  node [shape=none, fontname=\"Helvetica\", fontsize=10];\n";
        ofs << "  edge [fontname=\"Helvetica\", fontsize=9, penwidth=1.5];\n";

        ofs << "  subgraph cluster_callers {\n";
        ofs << "    label=\"Methods with tainted parameters\";\n";
        ofs << "    fontname=\"Helvetica\"; fontsize=12; fontcolor=\"#1a5276\";\n";
        ofs << "    style=rounded; fillcolor=\"#eaf4fb\";"
               " color=\"#2471a3\"; penwidth=2;\n";
        for (std::size_t i = 0; i < caller_list.size(); ++i) {
            const auto& mid = caller_list[i];
            ofs << "    c" << i << " [label=<"
                << node_html_label(mid, "#1a5276", "white", apk_label(mid))
                << ">, tooltip=\"" << node_tooltip(mid) << "\"];\n";
        }
        ofs << "  }\n\n";

        ofs << "  subgraph cluster_sinks {\n";
        ofs << "    label=\"Dangerous / IPC sink APIs\";\n";
        ofs << "    fontname=\"Helvetica\"; fontsize=12; fontcolor=\"#922b21\";\n";
        ofs << "    style=rounded; fillcolor=\"#fdedec\";"
               " color=\"#922b21\"; penwidth=2;\n";
        for (std::size_t i = 0; i < sink_list.size(); ++i) {
            const auto& mid = sink_list[i];
            const bool ipc = is_interapp_sink(mid.type.descriptor);
            ofs << "    s" << i << " [label=<"
                << node_html_label(mid, ipc ? "#d35400" : "#7b241c", "white",
                                   sink_origin_label(mid.type.descriptor))
                << ">, tooltip=\"" << node_tooltip(mid) << "\"];\n";
        }
        ofs << "  }\n\n";

        for (const auto& kv : edge_map) {
            const auto& me = kv.second;
            auto lbl = make_edge_label(me.tainted_args, me.offsets,
                                       sink_list[me.si].descriptor);
            const bool ipc = is_interapp_sink(sink_list[me.si].type.descriptor);
            ofs << "  c" << me.ci << " -> s" << me.si
                << " [label=\"" << lbl << "\","
                << " color=\"" << (ipc ? "#e67e22" : "#e74c3c") << "\","
                << " fontcolor=\"" << (ipc ? "#d35400" : "#922b21") << "\","
                   " arrowhead=vee];\n";
        }

        ofs << "\n  subgraph cluster_legend {\n";
        ofs << "    label=\"Legend\"; style=rounded; fontsize=9;\n";
        ofs << "    fontname=\"Helvetica\"; color=\"#aaaaaa\"; fillcolor=\"#f5f5f5\";\n";
        ofs << "    node [shape=plaintext, fontsize=9, fontname=\"Helvetica\"];\n";
        ofs << "    leg [label=\""
               "Blue header   = app method that passes tainted param to a sink\\n"
               "Red header    = dangerous API sink (exec / file / network / ...)\\n"
               "Orange header = inter-app IPC sink (Intent / ContentResolver)\\n"
               "Solid arrow   = tainted argument flowing to sink\\n"
               "  arg 0 = this (virtual), arg 1 = first param, ...\"];\n";
        ofs << "  }\n";
        ofs << "}\n";
    }

    ofs.close();
    std::cerr << "[+] Wrote taint call graph to "
              << fs::absolute(graph_out).string() << " ("
              << interproc.sink_hits.size() << " param-taint sink hit(s), "
              << interproc.source_sink_hits.size() << " source-to-sink hit(s), "
              << chains.size() << " IPC chain(s))\n";
}

// Collect JVM type descriptors for Android components that are explicitly
// disabled in their APK's AndroidManifest.xml (android:enabled="false").
// These components can never be reached at runtime, so seeding their methods
// as taint sources only produces false positives.
static std::vector<std::string>
collect_disabled_component_prefixes(virtual_machine& vm)
{
    std::vector<std::string> result;
    const auto& lg = vm.loaders();
    for (const auto& lv : boost::make_iterator_range(vertices(lg))) {
        const auto* info = get<apk_info>(&lg[lv].info);
        if (!info) {
            continue;
        }

        boost::property_tree::ptree app_pt;
        try {
            app_pt = info->manifest_ptree().get_child("application");
        }
        catch (...) {
            continue;
        }

        const auto& pkg = info->package_name();

        auto check_component = [&](const std::string& comp_type) {
            for (const auto& x : child_elements(app_pt, comp_type)) {
                auto enabled = x.second.get_optional<std::string>(
                        "<xmlattr>.android:enabled");
                if (!enabled || *enabled != "false") {
                    continue;
                }
                auto name_opt = x.second.get_optional<std::string>(
                        "<xmlattr>.android:name");
                if (!name_opt) {
                    continue;
                }
                std::string name = *name_opt;
                // Resolve relative names against the package.
                if (!name.empty() && name[0] == '.') {
                    name = pkg + name;
                }
                else if (name.find('.') == std::string::npos) {
                    name = pkg + '.' + name;
                }
                // Convert Java class name → JVM descriptor
                // (de.ecspride.Foo → Lde/ecspride/Foo;).
                std::string desc = "L";
                for (char c : name) {
                    desc += (c == '.') ? '/' : c;
                }
                desc += ';';
                result.push_back(std::move(desc));
            }
        };

        check_component("activity");
        check_component("service");
        check_component("receiver");
    }
    return result;
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
                         " [--taint-graph FILE] <file.dex|app.apk> ...\n"
                      << "  --quiet, -q        Suppress verbose output"
                         " (taint graph still written if --taint-graph given).\n"
                      << "  --interproc-only   Skip per-method taint output;"
                         " run interprocedural analysis only.\n"
                      << "  --taint-graph FILE Write DOT graph of taint flows"
                         " to sinks to FILE.\n";
            return 2;
        }
        virtual_machine vm;
        // Create a bootstrap (stub) loader that holds Android/Java framework
        // placeholder classes.  All app loaders are children of this loader so
        // that superclass lookup (DFS on loader graph) can always resolve stubs
        // like BroadcastReceiver, Activity, etc.
        {
            class_loader bootstrap(BOOTSTRAP_LOADER_ID, "BootstrapLoader",
                                   std::vector<std::string>{}.begin(),
                                   std::vector<std::string>{}.end());
            vm.add_loader(bootstrap);
        }
        seed_placeholder_classes(vm);

        // Load each input file into its own loader (IDs 100, 101, ...).
        std::vector<DexSources> all_sources;
        std::unordered_map<uint8_t, std::string> loader_names;
        for (std::size_t pi = 0; pi < positional.size(); ++pi) {
            const auto& input_path = positional[pi];
            auto sources = prepare_dex_sources(input_path);
            uint8_t loader_id = static_cast<uint8_t>(LOADER_ID + pi);
            loader_names[loader_id] = input_path;
            if (!wire_loader(vm, sources.files, input_path, quiet,
                             loader_id, sources.apk_dir)) {
                std::cerr << "[-] Failed to wire loader for: " << input_path
                          << "\n";
                return 1;
            }
            all_sources.push_back(std::move(sources));
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
        // Exclude bundled framework/library packages from param-taint seeding
        // to suppress false positives from support libraries shipped inside APKs.
        // Source-to-sink detection is unaffected (runs in a separate domain).
        ipc_cfg.param_seed_exclude_prefixes = {
            "Landroid/support/",   // old Android Support Library
            "Landroidx/",          // AndroidX
            "Lcom/google/android/",// Google Play Services / Firebase
            "Lcom/google/gson/",
            "Lcom/squareup/",
            "Lokhttp3/",
            "Lretrofit2/",
            "Lkotlin/",
            "Lkotlinx/",
        };
        // Exclude Android components disabled in AndroidManifest.xml
        // (android:enabled="false") — they cannot be reached at runtime.
        for (auto& d : collect_disabled_component_prefixes(vm)) {
            ipc_cfg.param_seed_exclude_prefixes.push_back(std::move(d));
        }
        // Skip private methods with no callers: they are unreachable dead code.
        ipc_cfg.skip_private_no_callers = true;
        auto interproc = analysis::dfa::run_interproc_param_taint(vm, ipc_cfg);

        // Compute IPC chains before printing so the relay-sink filter below can
        // consult them.  Chains are also needed by the taint-graph writer.
        auto chains = compute_ipc_chains(vm, interproc, loader_names);

        // Relay sinks (putExtra / putExtras) only place tainted data into an
        // Intent — they are not a final exfiltration on their own.  Suppress
        // relay-only hits (both SinkHits and SourceHits) whose caller method
        // has no confirmed downstream IPC chain.  This removes FPs like
        // ComponentNotInManifest1 where the target activity is absent from
        // every loaded manifest so no chain is ever constructed.
        {
            std::set<std::string> chained_callers;
            for (const auto& ch : chains) {
                chained_callers.insert(
                        method_id_string(ch.sender_hit.caller));
            }
            auto is_relay = [](const std::string& name) {
                return name == "putExtra" || name == "putExtras";
            };
            // Filter param-taint SinkHits for relay methods.
            auto& ph = interproc.sink_hits;
            ph.erase(
                std::remove_if(ph.begin(), ph.end(),
                    [&](const analysis::dfa::SinkHit& h) {
                        return is_relay(h.callee.name)
                               && chained_callers.find(
                                      method_id_string(h.caller))
                                      == chained_callers.end();
                    }),
                ph.end());
            // Filter source-to-sink SourceHits for relay methods.
            auto& sh = interproc.source_sink_hits;
            sh.erase(
                std::remove_if(sh.begin(), sh.end(),
                    [&](const analysis::dfa::SourceHit& h) {
                        return is_relay(h.sink_callee.name)
                               && chained_callers.find(
                                      method_id_string(h.caller))
                                      == chained_callers.end();
                    }),
                sh.end());
        }

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

            // Print source-to-sink hits (relay hits already filtered above).
            std::cout << "\n[+] Source-to-sink flows\n";
            if (interproc.source_sink_hits.empty()) {
                std::cout << "    (none found)\n";
            } else {
                for (const auto& hit : interproc.source_sink_hits) {
                    auto caller_str = method_id_string(hit.caller);
                    auto src_str = method_id_string(hit.source_callee);
                    auto sink_str = method_id_string(hit.sink_callee);
                    std::ostringstream args_ss;
                    for (std::size_t i = 0; i < hit.tainted_args.size(); ++i) {
                        args_ss << "arg" << hit.tainted_args[i];
                        if (i + 1 < hit.tainted_args.size()) args_ss << ",";
                    }
                    std::cout << "    [in " << caller_str << "] "
                              << (hit.source_callee.name.empty()
                                          ? "<source>" : src_str)
                              << " -> " << sink_str
                              << " (" << args_ss.str() << ")"
                              << " @off " << hit.sink_offset << "\n";
                }
            }
        }
        if (!quiet && !chains.empty()) {
            std::cout << "\n[+] Inter-app IPC chains (" << chains.size()
                      << " found)\n";
            for (const auto& ch : chains) {
                std::cout << "    " << method_id_string(ch.sender_hit.caller)
                          << " -> " << ch.sender_hit.callee.name
                          << " ~~[IPC]~~ "
                          << method_id_string(ch.receiver_entry)
                          << " [" << ch.receiver_apk_name << "]";
                if (!ch.receiver_sink_hits.empty()) {
                    std::cout << " -> "
                              << ch.receiver_sink_hits.size()
                              << " downstream sink(s)";
                }
                std::cout << "\n";
            }
        }

        // --- Write taint graph (independent of --quiet) ---
        if (!graph_out.empty()) {
            if (interproc.sink_hits.empty()
                && interproc.source_sink_hits.empty()) {
                std::cerr << "[-] No sink hits found; graph file not written.\n";
                return 1;
            }
            write_taint_graph(graph_out, interproc, loader_names, chains);
        }

        return 0;
    } catch (const std::exception& e) {
        std::cerr << "Error: " << e.what() << "\n";
        return 3;
    }
}
