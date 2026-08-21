#include "jitana/analysis/interproc_param_taint.hpp"

#include <algorithm>
#include <queue>

#include <boost/functional/hash.hpp>
#include <boost/optional.hpp>
#include <boost/type_erasure/any_cast.hpp>

#include "jitana/vm_core/insn_info.hpp"
#include "jitana/analysis/call_graph.hpp"

namespace jitana {
namespace analysis {
namespace dfa {
namespace {
    using DepSet = boost::dynamic_bitset<>;
    using RegDeps = std::vector<DepSet>;

    // Context for a method analysis: which of its params are tainted at entry.
    // Bit i = true means param i is tainted coming in from the caller.
    using CallContext = boost::dynamic_bitset<>;

    // Maps a composite field key to the set of source params that taint that
    // field within the current method analysis.  Keys have two forms:
    //   "R{reg_idx}:{fkey}"  — instance field on object in register reg_idx
    //   "STATIC:{fkey}"      — static field (no object register)
    // where fkey = "Ltype;.name:Ftype;".
    using FieldTaintMap = std::unordered_map<std::string, DepSet>;

    static bool is_iget(opcode op)
    {
        switch (op) {
        case opcode::op_iget:
        case opcode::op_iget_wide:
        case opcode::op_iget_object:
        case opcode::op_iget_boolean:
        case opcode::op_iget_byte:
        case opcode::op_iget_char:
        case opcode::op_iget_short:
            return true;
        default:
            return false;
        }
    }

    static bool is_iput(opcode op)
    {
        switch (op) {
        case opcode::op_iput:
        case opcode::op_iput_wide:
        case opcode::op_iput_object:
        case opcode::op_iput_boolean:
        case opcode::op_iput_byte:
        case opcode::op_iput_char:
        case opcode::op_iput_short:
            return true;
        default:
            return false;
        }
    }

    static bool is_sget(opcode op)
    {
        switch (op) {
        case opcode::op_sget:
        case opcode::op_sget_wide:
        case opcode::op_sget_object:
        case opcode::op_sget_boolean:
        case opcode::op_sget_byte:
        case opcode::op_sget_char:
        case opcode::op_sget_short:
            return true;
        default:
            return false;
        }
    }

    static bool is_sput(opcode op)
    {
        switch (op) {
        case opcode::op_sput:
        case opcode::op_sput_wide:
        case opcode::op_sput_object:
        case opcode::op_sput_boolean:
        case opcode::op_sput_byte:
        case opcode::op_sput_char:
        case opcode::op_sput_short:
            return true;
        default:
            return false;
        }
    }

    static bool is_aget(opcode op)
    {
        switch (op) {
        case opcode::op_aget:
        case opcode::op_aget_wide:
        case opcode::op_aget_object:
        case opcode::op_aget_boolean:
        case opcode::op_aget_byte:
        case opcode::op_aget_char:
        case opcode::op_aget_short:
            return true;
        default:
            return false;
        }
    }

    static bool is_aput(opcode op)
    {
        switch (op) {
        case opcode::op_aput:
        case opcode::op_aput_wide:
        case opcode::op_aput_object:
        case opcode::op_aput_boolean:
        case opcode::op_aput_byte:
        case opcode::op_aput_char:
        case opcode::op_aput_short:
            return true;
        default:
            return false;
        }
    }

    // Stable string key for a field: "Ltype;.name:Ftype;"
    //
    // vm.make_jvm_hdl(dex_field_hdl) re-decodes the field's class/name/type
    // strings straight out of the dex string pool on every call (no caching
    // in the vm_core layer). This function is called on every iget/iput/
    // sget/sput instruction, on every fixed-point iteration, for every
    // (method, context) pair the context-sensitive analysis explores — which
    // for real-world apps can be a very large number of calls for the exact
    // same instruction. Profiling a hung TaintBench run (chulia.apk) showed
    // ~30% of total runtime in this string rebuilding alone. A given
    // dex_field_hdl's (file, idx) pair always denotes the same field for the
    // process lifetime, so the result is safe to memoize globally.
    static std::string get_field_key(virtual_machine& vm, const insn& insn_obj)
    {
        auto fhdl_ptr = const_val<dex_field_hdl>(insn_obj);
        if (!fhdl_ptr) {
            return "";
        }
        static std::unordered_map<uint32_t, std::string> cache;
        auto key = static_cast<uint32_t>(*fhdl_ptr);
        auto it = cache.find(key);
        if (it != cache.end()) {
            return it->second;
        }
        auto jfhdl = vm.make_jvm_hdl(*fhdl_ptr);
        auto result = jfhdl.type_hdl.descriptor + "." + jfhdl.unique_name;
        cache.emplace(key, result);
        return result;
    }

    // Keys for the object-sensitive FieldTaintMap:
    //   intra-method: "R{reg}:{fkey}" or "STATIC:{fkey}"
    //   inter-method (field_write_deps): "P{param}:{fkey}" or "STATIC:{fkey}"
    static std::string make_instance_field_taint_key(std::size_t reg_idx,
                                                     const std::string& fkey)
    {
        return "R" + std::to_string(reg_idx) + ":" + fkey;
    }

    static std::string make_static_field_taint_key(const std::string& fkey)
    {
        return "STATIC:" + fkey;
    }

    // Used in field_write_deps to record which callee param holds the object.
    static std::string make_field_write_key(std::size_t param_idx,
                                            const std::string& fkey)
    {
        return "P" + std::to_string(param_idx) + ":" + fkey;
    }

    // Parse "R{n}:{fkey}" or "P{n}:{fkey}" → {n, fkey}.
    // Returns false if malformed.
    static bool parse_indexed_field_key(const std::string& k,
                                        std::size_t& out_idx,
                                        std::string& out_fkey)
    {
        if (k.size() < 3) return false;
        auto colon = k.find(':');
        if (colon == std::string::npos || colon < 2) return false;
        try {
            out_idx = std::stoul(k.substr(1, colon - 1));
        } catch (...) {
            return false;
        }
        out_fkey = k.substr(colon + 1);
        return true;
    }

    std::pair<std::string, std::string>
    split_unique_name(const std::string& unique_name)
    {
        auto pos = unique_name.find('(');
        if (pos == std::string::npos) {
            return {unique_name, ""};
        }
        return {unique_name.substr(0, pos), unique_name.substr(pos)};
    }

    MethodId make_method_id_local(const jvm_method_hdl& hdl)
    {
        auto parts = split_unique_name(hdl.unique_name);
        return MethodId{hdl.type_hdl, parts.first, parts.second};
    }

    // Same rationale/caching as get_field_key below: vm.make_jvm_hdl(dex_method_hdl)
    // re-decodes the method's class/name/descriptor straight out of the dex
    // string pool on every call, and this runs once per invoke instruction
    // per fixed-point iteration per (method, context) pair explored — by far
    // the hottest path in the whole analysis (see get_field_key's comment).
    // A given dex_method_hdl's (file, idx) always denotes the same method for
    // the process lifetime, so memoize globally.
    MethodId make_method_id_local(const virtual_machine& vm,
                                  const dex_method_hdl& hdl)
    {
        static std::unordered_map<uint32_t, MethodId> cache;
        auto key = static_cast<uint32_t>(hdl);
        auto it = cache.find(key);
        if (it != cache.end()) {
            return it->second;
        }
        auto result = make_method_id_local(vm.make_jvm_hdl(hdl));
        cache.emplace(key, result);
        return result;
    }

    bool normalize_reg(const register_idx& reg,
                       std::size_t reg_domain,
                       std::size_t& out_idx)
    {
        if (!reg.valid() || reg.is_result() || reg.is_exception()) {
            return false;
        }
        const auto raw = static_cast<int32_t>(reg);
        if (raw < 0) {
            return false;
        }
        const auto idx = static_cast<std::size_t>(raw);
        if (idx >= reg_domain) {
            return false;
        }
        out_idx = idx;
        return true;
    }

    std::vector<insn_vertex_descriptor>
    build_order(const insn_graph& ig)
    {
        std::vector<insn_vertex_descriptor> order;
        order.reserve(num_vertices(ig));
        for (auto it = vertices(ig); it.first != it.second; ++it.first) {
            order.push_back(*it.first);
        }
        return order;
    }

    enum class InvokeKind { kStatic, kDirect, kVirtual, kInterface, kUnknown };

    InvokeKind opcode_invoke_kind(opcode op)
    {
        switch (op) {
        case opcode::op_invoke_static:
        case opcode::op_invoke_static_range:
            return InvokeKind::kStatic;
        case opcode::op_invoke_direct:
        case opcode::op_invoke_direct_range:
        case opcode::op_invoke_super:
        case opcode::op_invoke_super_range:
        case opcode::op_invoke_object_init_range:
            return InvokeKind::kDirect;
        case opcode::op_invoke_interface:
        case opcode::op_invoke_interface_range:
            return InvokeKind::kInterface;
        case opcode::op_invoke_virtual:
        case opcode::op_invoke_virtual_range:
        case opcode::op_invoke_virtual_quick:
        case opcode::op_invoke_virtual_quick_range:
            return InvokeKind::kVirtual;
        default:
            return InvokeKind::kUnknown;
        }
    }

    bool is_range_invoke(opcode op)
    {
        switch (op) {
        case opcode::op_invoke_direct_range:
        case opcode::op_invoke_interface_range:
        case opcode::op_invoke_static_range:
        case opcode::op_invoke_super_range:
        case opcode::op_invoke_virtual_range:
        case opcode::op_invoke_object_init_range:
        case opcode::op_invoke_virtual_quick_range:
        case opcode::op_invoke_super_quick_range:
            return true;
        default:
            return false;
        }
    }

    std::vector<std::size_t>
    parse_invoke_args(opcode op, const insn& insn, std::size_t reg_domain)
    {
        std::vector<std::size_t> args;
        const auto regs_range = regs(insn);
        if (is_range_invoke(op)) {
            if (!regs_range.empty()) {
                auto first = regs_range.front();
                auto last = regs_range.back();
                if (first.valid() && last.valid()) {
                    auto start = static_cast<int32_t>(first);
                    auto end = static_cast<int32_t>(last);
                    if (start >= 0 && end >= start) {
                        for (auto r = start; r <= end; ++r) {
                            if (static_cast<std::size_t>(r) < reg_domain) {
                                args.push_back(static_cast<std::size_t>(r));
                            }
                        }
                    }
                }
            }
            return args;
        }
        for (const auto& reg : regs_range) {
            std::size_t idx;
            if (normalize_reg(reg, reg_domain, idx)) {
                args.push_back(idx);
            }
        }
        return args;
    }

    struct InvokeInfo {
        MethodId callee;
        dex_method_hdl callee_hdl;
        InvokeKind kind{InvokeKind::kUnknown};
        std::vector<std::size_t> args;
        bool resolved{false};
    };

    boost::optional<InvokeInfo> parse_invoke(virtual_machine& vm,
                                             const insn& insn,
                                             std::size_t reg_domain)
    {
        const auto op_val = op(insn);
        if (!info(op_val).can_invoke()) {
            return boost::none;
        }
        auto method_hdl = const_val<dex_method_hdl>(insn);
        if (method_hdl == nullptr) {
            return boost::none;
        }
        InvokeInfo inv;
        inv.callee_hdl = *method_hdl;
        inv.callee = make_method_id_local(vm, *method_hdl);
        inv.kind = opcode_invoke_kind(op_val);
        inv.args = parse_invoke_args(op_val, insn, reg_domain);
        if (auto mv = vm.find_method(*method_hdl, false)) {
            inv.callee = make_method_id_local(vm.methods()[*mv].jvm_hdl);
            inv.resolved = true;
        }
        return inv;
    }

    // Collects all transitive supertype descriptors of a class (including
    // itself) into `out`.  Walks up the class inheritance graph via in_edges:
    // class_super_edge_property edges run super → sub, so the source of an
    // in_edge of vertex v is v's direct superclass or interface.
    static void collect_supertype_descriptors(
            class_vertex_descriptor start,
            const class_graph& cg,
            std::unordered_set<std::string>& out)
    {
        std::queue<class_vertex_descriptor> q;
        q.push(start);
        out.insert(cg[start].jvm_hdl.descriptor);
        while (!q.empty()) {
            auto cur = q.front();
            q.pop();
            for (const auto& e :
                 boost::make_iterator_range(in_edges(cur, cg))) {
                const auto* prop = boost::type_erasure::any_cast<
                        const class_super_edge_property*>(&cg[e]);
                if (prop == nullptr) {
                    continue;
                }
                auto parent = source(e, cg);
                const auto& pdesc = cg[parent].jvm_hdl.descriptor;
                if (out.insert(pdesc).second) {
                    q.push(parent);
                }
            }
        }
    }

    std::vector<method_vertex_descriptor>
    collect_virtual_targets(const method_vertex_descriptor& base,
                            const method_graph& mg)
    {
        std::vector<method_vertex_descriptor> targets;
        std::queue<method_vertex_descriptor> q;
        std::vector<bool> visited(num_vertices(mg), false);
        q.push(base);
        visited[base] = true;
        while (!q.empty()) {
            auto cur = q.front();
            q.pop();
            targets.push_back(cur);
            for (const auto& e : boost::make_iterator_range(out_edges(cur, mg))) {
                const auto* prop = boost::type_erasure::any_cast<
                        const method_super_edge_property*>(&mg[e]);
                if (prop == nullptr) {
                    continue;
                }
                auto nxt = target(e, mg);
                if (!visited[nxt]) {
                    visited[nxt] = true;
                    q.push(nxt);
                }
            }
        }
        return targets;
    }

    struct CallGraph {
        std::unordered_map<MethodId, method_vertex_descriptor, MethodIdHash>
                method_vertices;
        std::unordered_map<CallSiteId, std::vector<MethodId>, CallSiteIdHash>
                callees;
        std::unordered_map<MethodId, std::vector<CallSiteId>, MethodIdHash>
                callers;
        std::unordered_map<MethodId, std::vector<CallSiteId>, MethodIdHash>
                outgoing;
    };

    void add_edge(CallGraph& cg, const CallSiteId& cs, const MethodId& callee)
    {
        auto& list = cg.callees[cs];
        if (std::find(list.begin(), list.end(), callee) == list.end()) {
            list.push_back(callee);
        }
        cg.callers[callee].push_back(cs);
        auto& out_edges = cg.outgoing[cs.caller];
        if (std::find(out_edges.begin(), out_edges.end(), cs) == out_edges.end()) {
            out_edges.push_back(cs);
        }
    }

    CallGraph build_call_graph(virtual_machine& vm)
    {
        CallGraph cg;
        add_call_graph_edges(vm);
        auto& mg = vm.methods();
        for (const auto& mv : boost::make_iterator_range(vertices(mg))) {
            cg.method_vertices[make_method_id_local(mg[mv].jvm_hdl)] = mv;
        }

        for (const auto& mv : boost::make_iterator_range(vertices(mg))) {
            const auto mid = make_method_id_local(mg[mv].jvm_hdl);
            const auto& ig = mg[mv].insns;
            for (const auto& e : boost::make_iterator_range(out_edges(mv, mg))) {
                auto* prop = boost::type_erasure::any_cast<method_call_edge_property*>(
                        &mg[e]);
                if (prop == nullptr) {
                    continue;
                }
                auto tgt = target(e, mg);
                CallSiteId cs{mid, ig[prop->caller_insn_vertex].off};

                if (prop->virtual_call) {
                    // Expand virtual/interface dispatch via CHA: collect all
                    // known overriding implementations reachable from the
                    // statically declared target through method_super_edge_property
                    // (override) edges.
                    for (auto override_mv : collect_virtual_targets(tgt, mg)) {
                        add_edge(cg, cs,
                                 make_method_id_local(mg[override_mv].jvm_hdl));
                    }
                } else {
                    add_edge(cg, cs, make_method_id_local(mg[tgt].jvm_hdl));
                }
            }
        }
        return cg;
    }

    MethodSummary stub_summary(std::size_t param_count, LibPolicy policy)
    {
        MethodSummary s;
        s.param_count = param_count;
        s.return_dep = DepSet(param_count);
        if (policy == LibPolicy::Conservative) {
            s.return_dep.set();
        }
        return s;
    }

    // -------------------------------------------------------------------------
    // Context-sensitive analysis
    //
    // A CallContext is a bitset recording which of a method's parameters are
    // known to be tainted when the method is called.  Instead of computing one
    // summary per method (context-insensitive), we compute one summary per
    // (method, CallContext) pair and memoize the results.  This eliminates
    // false positives that arise from library stubs and non-tainted arguments
    // being treated the same as tainted ones in the context-insensitive version.
    // -------------------------------------------------------------------------

    // Hash a CallContext (dynamic_bitset) by its set bits.
    static std::size_t hash_call_context(const CallContext& ctx)
    {
        std::size_t h = ctx.size();
        for (auto pos = ctx.find_first(); pos != CallContext::npos;
             pos = ctx.find_next(pos)) {
            boost::hash_combine(h, pos);
        }
        return h;
    }

    struct CtxKey {
        MethodId mid;
        CallContext ctx;
        // Which of this method's params are source-API-derived (e.g. from
        // getStringExtra/getSimCountryIso) at this call site. Distinct from
        // ctx (generic param-taint) so a call with source-tainted args isn't
        // conflated with — or its summary reused for — a call without them.
        CallContext src_ctx;
        bool operator==(const CtxKey& o) const
        {
            return mid == o.mid && ctx == o.ctx && src_ctx == o.src_ctx;
        }
    };

    struct CtxKeyHash {
        std::size_t operator()(const CtxKey& k) const
        {
            std::size_t h = MethodIdHash{}(k.mid);
            boost::hash_combine(h, hash_call_context(k.ctx));
            boost::hash_combine(h, hash_call_context(k.src_ctx));
            return h;
        }
    };

    // Memoization table for context-sensitive summaries.
    struct CtxCache {
        std::unordered_map<CtxKey, MethodSummary, CtxKeyHash> summaries;
        std::unordered_set<CtxKey, CtxKeyHash> in_progress;
        // Optimistic (bottom-of-lattice) summaries for in-progress methods.
        // Returned to callers in recursive cycles; grows toward fixed point.
        std::unordered_map<CtxKey, MethodSummary, CtxKeyHash> interim;
        // Ordered analysis stack (back = innermost in-progress method).
        std::vector<CtxKey> call_stack;
        // Callee cache entries added while each in-progress method was being
        // analysed. Evicted when the method's interim summary changes.
        std::unordered_map<CtxKey, std::vector<CtxKey>, CtxKeyHash> added_during;
        // Lazily-built supertype descriptor sets for subtype sink matching.
        // Maps a class descriptor to the set of all its transitive supertype
        // descriptors (including itself).
        std::unordered_map<std::string, std::unordered_set<std::string>>
                supertype_cache;
        // Safety valve against the optimistic-fixed-point's cache-eviction
        // cascade: added_during eviction is necessary for correctness on
        // genuine mutual-recursion cycles (a callee's summary computed
        // against a still-growing enclosing interim really can go stale),
        // but it evicts every summary touched during an iteration, not just
        // ones that actually depended on the cycle. For a tight recursive
        // cluster this can blow up to roughly MAX_ITER^depth re-computation
        // even when the total number of distinct (method,context) pairs
        // involved is tiny — observed hanging TaintBench's chulia.apk (a
        // small open-source Base64 library with a few mutually-recursive
        // methods) indefinitely despite fewer than 500 total analyses ever
        // completing. compute_calls counts compute_summary_ctx invocations
        // since it was last reset (once per top-level seed method / lifecycle
        // callback — see run_interproc_param_taint); once it crosses
        // kComputeBudget, get_or_compute_ctx stops starting fresh analyses
        // and falls back to the same conservative stub already used for
        // unmodeled library methods, bounding worst-case work per seed
        // instead of fixing the underlying over-eager invalidation (see
        // memory for the precise "cycle-touch" fix considered and deferred).
        std::size_t compute_calls = 0;
        static constexpr std::size_t kComputeBudget = 20000;
    };

    // Forward declaration — compute_summary_ctx and get_or_compute_ctx are
    // mutually recursive.
    static MethodSummary get_or_compute_ctx(
            virtual_machine& vm,
            const MethodId& mid,
            const CallGraph& cg,
            const CallContext& ctx,
            const CallContext& src_ctx,
            CtxCache& cache,
            LibPolicy lib_policy,
            const std::vector<SinkSpec>& sinks,
            std::vector<SinkHit>& sink_hits,
            const std::vector<SourceSpec>& sources,
            std::vector<SourceHit>& source_sink_hits);

    // Intra-method dataflow analysis for one (method, entry context) pair.
    // entry_ctx specifies which of the method's own params are tainted at entry.
    // entry_src_ctx specifies which of the method's own params are source-API
    // -derived (e.g. getStringExtra) at entry, because the caller passed a
    // source-tainted actual argument for that parameter. Distinct from
    // pre_src_field_taint, which is about FIELD state carried across lifecycle
    // phases, not per-parameter state carried across a single call.
    // pre_src_field_taint seeds the source-taint field map before the fixed-point
    // loop; used in the lifecycle second pass to carry source-tainted field state
    // from prior lifecycle callbacks into the current one.
    // Calls back into get_or_compute_ctx for each callee encountered.
    static MethodSummary compute_summary_ctx(
            virtual_machine& vm,
            const MethodId& mid,
            const method_vertex_descriptor& mv,
            const CallGraph& cg,
            const CallContext& entry_ctx,
            const CallContext& entry_src_ctx,
            const std::unordered_set<std::string>& pre_src_field_taint,
            CtxCache& cache,
            LibPolicy lib_policy,
            const std::vector<SinkSpec>& sinks,
            std::vector<SinkHit>& sink_hits,
            const std::vector<SourceSpec>& sources,
            std::vector<SourceHit>& source_sink_hits)
    {
        ++cache.compute_calls;
        MethodSummary sum;
        const auto& mg = vm.methods();
        const auto& ig = mg[mv].insns;
        const auto order = build_order(ig);
        sum.param_count = ig[boost::graph_bundle].ins_size;
        sum.return_dep = DepSet(sum.param_count);
        if (order.empty()) {
            return sum;
        }

        const auto reg_domain = ig[boost::graph_bundle].registers_size;
        const std::size_t n = order.size();

        auto make_zero_frame = [&]() {
            return RegDeps(reg_domain, DepSet(sum.param_count));
        };
        std::vector<RegDeps> IN(n, make_zero_frame());
        std::vector<RegDeps> OUT(n, make_zero_frame());
        std::vector<DepSet> pending(n, DepSet(sum.param_count));

        // Precompute defs/uses.
        std::vector<std::vector<std::size_t>> DEF(n);
        std::vector<std::vector<std::size_t>> USE(n);
        for (std::size_t i = 0; i < n; ++i) {
            const auto& insn_obj = ig[order[i]].insn;
            const auto& iinfo = info(op(insn_obj));
            for (const auto& reg : defs(insn_obj)) {
                std::size_t idx;
                if (normalize_reg(reg, reg_domain, idx)) {
                    DEF[i].push_back(idx);
                    // Wide defs (long/double) occupy two consecutive registers.
                    if (iinfo.sets_wide_register() && idx + 1 < reg_domain) {
                        DEF[i].push_back(idx + 1);
                    }
                }
            }
            for (const auto& reg : uses(insn_obj)) {
                std::size_t idx;
                if (normalize_reg(reg, reg_domain, idx)) {
                    USE[i].push_back(idx);
                    // Wide uses (long/double) span two consecutive registers.
                    if (iinfo.reads_wide_register() && idx + 1 < reg_domain) {
                        USE[i].push_back(idx + 1);
                    }
                }
            }
            auto dedup = [](auto& vec) {
                std::sort(vec.begin(), vec.end());
                vec.erase(std::unique(vec.begin(), vec.end()), vec.end());
            };
            dedup(DEF[i]);
            dedup(USE[i]);
        }

        const auto vertex_count = static_cast<std::size_t>(num_vertices(ig));
        std::vector<std::size_t> index_of(vertex_count, n);
        for (std::size_t i = 0; i < n; ++i) {
            if (order[i] < index_of.size()) {
                index_of[order[i]] = i;
            }
        }

        // Seed only the parameters listed in entry_ctx.
        RegDeps param_seed = make_zero_frame();
        if (sum.param_count <= reg_domain) {
            const auto start = reg_domain - sum.param_count;
            for (std::size_t i = 0; i < sum.param_count; ++i) {
                if (i < entry_ctx.size() && entry_ctx.test(i)) {
                    param_seed[start + i].set(i);
                }
            }
        }

        // Seed only the parameters listed in entry_src_ctx: mirrors param_seed
        // above, but for the source-taint domain (which params are derived
        // from a known source API in the caller, e.g. getStringExtra).
        std::vector<uint8_t> src_param_seed(reg_domain, 0);
        if (sum.param_count <= reg_domain) {
            const auto start = reg_domain - sum.param_count;
            for (std::size_t i = 0; i < sum.param_count; ++i) {
                if (i < entry_src_ctx.size() && entry_src_ctx.test(i)) {
                    src_param_seed[start + i] = 1;
                }
            }
        }

        // Flow-insensitive field taint: tracks which source params taint each
        // field within this method.  Grows monotonically; convergence is
        // guaranteed.  Keyed by stable JVM field descriptor.
        FieldTaintMap field_taint;

        // Source-taint field map: "R{reg}:{fkey}" or "STATIC:{fkey}" entries
        // indicate that a field read from that (object,field) pair carries
        // source-API-derived data.  Seeded from pre_src_field_taint (lifecycle
        // predecessor context); grows monotonically during the fixed-point loop.
        std::unordered_set<std::string> src_field_taint;
        if (!pre_src_field_taint.empty() && sum.param_count <= reg_domain) {
            const auto param_start = reg_domain - sum.param_count;
            for (const auto& pk : pre_src_field_taint) {
                if (pk.rfind("STATIC:", 0) == 0) {
                    src_field_taint.insert(pk);
                } else if (pk.rfind("FIELD:", 0) == 0) {
                    src_field_taint.insert(pk);
                } else if (!pk.empty() && pk[0] == 'P') {
                    std::size_t param_idx;
                    std::string fkey;
                    if (parse_indexed_field_key(pk, param_idx, fkey)
                        && param_idx < sum.param_count) {
                        src_field_taint.insert(make_instance_field_taint_key(
                                param_start + param_idx, fkey));
                    }
                }
            }
        }

        auto is_sink = [&](const MethodId& m) {
            for (const auto& spec : sinks) {
                if (m.name != spec.name || m.descriptor != spec.descriptor) {
                    continue;
                }
                // Fast path: exact class match.
                if (m.type.descriptor == spec.type_descriptor) {
                    return true;
                }
                // Subtype match: m.type is a subtype of spec.type_descriptor.
                // Look up (or lazily build) the full supertype set for m.type.
                auto& supertypes = cache.supertype_cache[m.type.descriptor];
                if (supertypes.empty()) {
                    // m.type is keyed to the callee's own dex/app loader, but
                    // framework stub classes (e.g. OutputStreamWriter) are
                    // only ever registered under the bootstrap loader's own
                    // handle (seed_placeholder_classes) and never reached by
                    // ordinary inheritance resolution from the app's classes.
                    // A bare jvm_hdl_to_vertex lookup keyed on m.type's own
                    // loader therefore misses them; vm.find_class walks the
                    // loader parent chain (app -> bootstrap) so it finds
                    // bootstrap-registered placeholders too, and caches the
                    // result under m.type for subsequent lookups.
                    if (auto cv = vm.find_class(m.type, false)) {
                        collect_supertype_descriptors(*cv, vm.classes(),
                                                      supertypes);
                    } else {
                        supertypes.insert(m.type.descriptor);
                    }
                }
                if (supertypes.count(spec.type_descriptor)) {
                    return true;
                }
            }
            return false;
        };

        // Check whether a MethodId is a known source API.
        // Returns a pointer to the matching SourceSpec, or nullptr.
        auto is_source = [&](const MethodId& m) -> const SourceSpec* {
            for (const auto& spec : sources) {
                if (m.name == spec.name
                    && m.descriptor == spec.descriptor
                    && m.type.descriptor == spec.type_descriptor) {
                    return &spec;
                }
            }
            return nullptr;
        };

        // ---- Source-taint domain ----------------------------------------
        // SRC_OUT[i][r]: register r holds source-API-derived data after insn i.
        using SrcFrame = std::vector<uint8_t>;
        auto make_src = [&]() { return SrcFrame(reg_domain, 0); };
        std::vector<SrcFrame> SRC_OUT(n, make_src());

        // Per-instruction: is this instruction a source API call?
        // Precomputed once (static property, doesn't change across iterations).
        std::vector<uint8_t> src_invoke(n, 0);
        std::vector<MethodId> src_invoke_callee(n);
        if (!sources.empty()) {
            for (std::size_t i = 0; i < n; ++i) {
                const auto vi = order[i];
                const auto& insn_obj2 = ig[vi].insn;
                if (info(op(insn_obj2)).can_invoke()) {
                    auto inv2 = parse_invoke(vm, insn_obj2, reg_domain);
                    if (inv2) {
                        CallSiteId cs2{mid, ig[vi].off};
                        auto tit = cg.callees.find(cs2);
                        auto check = [&](const MethodId& m) {
                            if (!src_invoke[i]) {
                                if (is_source(m)) {
                                    src_invoke[i] = 1;
                                    src_invoke_callee[i] = m;
                                }
                            }
                        };
                        if (tit != cg.callees.end()) {
                            for (const auto& tgt : tit->second) check(tgt);
                        } else {
                            check(inv2->callee);
                        }
                    }
                }
            }
        }

        // Per-register best-effort source-API origin (updated lazily).
        std::vector<MethodId> src_origin(reg_domain);

        // Per-instruction: does calling this instruction's callee return
        // source-API-derived data?  Updated during the fixed-point loop as
        // callee summaries are computed.  Distinct from src_invoke[] which
        // only covers direct source-API invocations.
        std::vector<uint8_t> src_callee_ret(n, 0);
        // Best-effort source API origin for callee-return source taint.
        std::vector<MethodId> src_callee_origin(n);

        bool changed = true;
        // Safety cap on the intraprocedural fixed point: DepSets are supposed
        // to only grow, which for a finite lattice guarantees convergence
        // within a small number of passes (bounded by param_count/register
        // count) — legitimate methods converge in single/low-double digits.
        // Observed TaintBench's chulia.apk (an open-source Base64 library)
        // oscillating non-monotonically in a 13-instruction constructor for
        // 1.7M+ iterations without ever converging, meaning some code path
        // violates the monotonic-growth invariant for that instruction shape
        // (root cause not identified — deferred; see project memory). The
        // outer interprocedural recursion already has an analogous cap
        // (get_or_compute_ctx's MAX_ITER=16), but nothing previously bounded
        // this inner per-method loop. kMaxInnerIter is set far above any
        // legitimate convergence count so it only trips on genuine
        // non-termination; when it trips, analysis proceeds with whatever
        // (possibly not fully converged) state exists rather than hanging.
        static constexpr std::size_t kMaxInnerIter = 5000;
        std::size_t inner_iters = 0;
        while (changed && inner_iters < kMaxInnerIter) {
            ++inner_iters;
            changed = false;
            for (std::size_t i = 0; i < n; ++i) {
                const auto v = order[i];
                auto new_in = make_zero_frame();
                DepSet incoming = DepSet(sum.param_count);
                bool saw_pred = false;
                SrcFrame new_src_in = make_src();
                uint8_t src_incoming = 0;
                MethodId src_incoming_callee;
                for (auto ee = in_edges(v, ig); ee.first != ee.second; ++ee.first) {
                    auto pred = source(*ee.first, ig);
                    if (pred < index_of.size()) {
                        auto pred_idx = index_of[pred];
                        if (pred_idx < n) {
                            for (std::size_t r = 0; r < reg_domain; ++r) {
                                new_in[r] |= OUT[pred_idx][r];
                                new_src_in[r] |= SRC_OUT[pred_idx][r];
                            }
                            incoming |= pending[pred_idx];
                            if ((src_invoke[pred_idx] || src_callee_ret[pred_idx])
                                && !src_incoming) {
                                src_incoming = 1;
                                if (src_invoke[pred_idx]) {
                                    src_incoming_callee =
                                            src_invoke_callee[pred_idx];
                                } else if (!src_callee_origin[pred_idx].name
                                                .empty()) {
                                    src_incoming_callee =
                                            src_callee_origin[pred_idx];
                                }
                            }
                            saw_pred = true;
                        }
                    }
                }
                if (!saw_pred) {
                    new_in = param_seed;
                    new_src_in = src_param_seed;
                }

                auto new_out = new_in;
                for (auto reg : DEF[i]) {
                    if (reg < new_out.size()) {
                        new_out[reg].reset();
                    }
                }

                SrcFrame new_src_out = new_src_in;
                for (auto reg : DEF[i]) {
                    if (reg < new_src_out.size()) {
                        new_src_out[reg] = 0;
                    }
                }

                DepSet use_dep(sum.param_count);
                for (auto reg : USE[i]) {
                    if (reg < new_in.size()) {
                        use_dep |= new_in[reg];
                    }
                }

                const auto& insn_obj = ig[v].insn;
                const auto opcode_val = op(insn_obj);

                DepSet new_pending(sum.param_count);

                if (info(opcode_val).can_invoke()) {
                    auto invoke = parse_invoke(vm, insn_obj, reg_domain);
                    if (invoke) {
                        // Report sink hit if any tainted arg reaches a sink.
                        // Also checks FieldTaintMap: Intent objects are often
                        // untainted as pointers but carry tainted extras stored
                        // via putExtra — the taint lives in field_taint entries
                        // keyed "R{reg}:...".  This is essential for detecting
                        // tainted IPC dispatch (startActivityForResult, etc.).
                        auto maybe_report_sink = [&](const MethodId& callee_mid) {
                            if (!is_sink(callee_mid)) return;
                            std::vector<std::size_t> tainted_args;
                            for (std::size_t ai = 0; ai < invoke->args.size();
                                 ++ai) {
                                auto arg_reg = invoke->args[ai];
                                bool reg_tainted = arg_reg < new_in.size()
                                                   && new_in[arg_reg].any();
                                if (!reg_tainted) {
                                    // Check if any field of this register
                                    // carries taint (e.g. Intent.putExtra).
                                    std::string prefix =
                                            "R" + std::to_string(arg_reg) + ":";
                                    for (const auto& kv : field_taint) {
                                        if (kv.first.rfind(prefix, 0) == 0
                                            && kv.second.any()) {
                                            reg_tainted = true;
                                            break;
                                        }
                                    }
                                }
                                if (reg_tainted) {
                                    tainted_args.push_back(ai);
                                }
                            }
                            if (!tainted_args.empty()) {
                                SinkHit hit;
                                hit.caller = mid;
                                hit.offset = ig[v].off;
                                hit.callee = callee_mid;
                                hit.tainted_args = std::move(tainted_args);
                                sink_hits.push_back(std::move(hit));
                            }
                        };

                        // Report source-to-sink hit if source-API-derived data
                        // reaches a sink argument.  Also propagates source-taint
                        // onto the receiver object: when putExtra(intent,key,val)
                        // is called with a tainted val, the intent register
                        // itself becomes source-tainted so downstream calls like
                        // startActivityForResult(intent,...) are also detected.
                        auto maybe_report_source_sink =
                                [&](const MethodId& callee_mid) {
                            if (sources.empty() || !is_sink(callee_mid)) return;
                            std::vector<std::size_t> src_tainted;
                            for (std::size_t ai = 0;
                                 ai < invoke->args.size(); ++ai) {
                                auto arg_reg = invoke->args[ai];
                                if (arg_reg < new_src_in.size()
                                    && new_src_in[arg_reg]) {
                                    src_tainted.push_back(ai);
                                }
                            }
                            if (!src_tainted.empty()) {
                                SourceHit hit;
                                hit.caller = mid;
                                hit.sink_offset = ig[v].off;
                                hit.sink_callee = callee_mid;
                                hit.tainted_args = src_tainted;
                                // Best-effort: get source origin from first
                                // tainted arg's src_origin entry.
                                for (auto ai : src_tainted) {
                                    auto ar = invoke->args[ai];
                                    if (ar < src_origin.size()
                                        && !src_origin[ar].name.empty()) {
                                        hit.source_callee = src_origin[ar];
                                        break;
                                    }
                                }
                                source_sink_hits.push_back(std::move(hit));

                                // Receiver contamination: if a non-receiver
                                // arg is source-tainted and the method is an
                                // instance method (arg 0 = receiver object),
                                // mark the receiver as source-tainted.
                                // This models putExtra(intent, key, tainted)
                                // → intent is now tainted, so downstream
                                // startActivityForResult(intent) is detected.
                                {
                                    bool has_non_rcv_src = false;
                                    for (auto ai : src_tainted) {
                                        if (ai > 0) {
                                            has_non_rcv_src = true;
                                            break;
                                        }
                                    }
                                    if (has_non_rcv_src
                                        && !invoke->args.empty()) {
                                        auto rcv = invoke->args[0];
                                        if (rcv < new_src_out.size()
                                            && !new_src_out[rcv]) {
                                            new_src_out[rcv] = 1;
                                        }
                                    }
                                }
                            }
                        };

                        CallSiteId cs{mid, ig[v].off};
                        auto targets_it = cg.callees.find(cs);
                        if (targets_it != cg.callees.end()) {
                            for (const auto& tgt : targets_it->second) {
                                maybe_report_sink(tgt);
                                maybe_report_source_sink(tgt);
                            }
                        } else {
                            maybe_report_sink(invoke->callee);
                            maybe_report_source_sink(invoke->callee);
                        }

                        // Derive the callee's context: which of its params
                        // are tainted based on the actual argument registers.
                        CallContext callee_ctx(invoke->args.size());
                        // Mirror callee_ctx for the source-taint domain: which
                        // of the callee's params are source-API-derived based
                        // on the actual argument registers at this call site.
                        // This is what lets e.g. saveData(intent.getStringExtra(...))
                        // detect the sink inside saveData as a proper
                        // source-to-sink flow instead of only a generic
                        // param-taint sink hit.
                        CallContext callee_src_ctx(invoke->args.size());
                        for (std::size_t pi = 0; pi < invoke->args.size();
                             ++pi) {
                            auto arg_reg = invoke->args[pi];
                            if (arg_reg < new_in.size()
                                && new_in[arg_reg].any()) {
                                callee_ctx.set(pi);
                            }
                            if (arg_reg < new_src_in.size()
                                && new_src_in[arg_reg]) {
                                callee_src_ctx.set(pi);
                            }
                        }

                        // Context-sensitive callee summary lookup.
                        std::vector<MethodId> callees_to_propagate;
                        if (targets_it != cg.callees.end()) {
                            callees_to_propagate = targets_it->second;
                        } else {
                            callees_to_propagate.push_back(invoke->callee);
                        }

                        for (const auto& tgt : callees_to_propagate) {
                            // System.arraycopy(src,srcPos,dst,dstPos,len):
                            // propagate taint from src (arg0) to dst (arg2).
                            // Taint lives in two places: the array reference
                            // register (new_in) AND the element field_taint
                            // entry keyed "R{reg}:[]" (from aput instructions).
                            if (tgt.type.descriptor == "Ljava/lang/System;"
                                && tgt.name == "arraycopy"
                                && invoke->args.size() >= 3) {
                                auto src_r = invoke->args[0];
                                auto dst_r = invoke->args[2];
                                // Propagate param-taint from src array to dst.
                                if (src_r < new_in.size()
                                    && new_in[src_r].any()
                                    && dst_r < new_out.size()) {
                                    new_out[dst_r] |= new_in[src_r];
                                    // Do NOT set changed=true here: new_out[dst_r]
                                    // starts from predecessors' OUT (not stored
                                    // OUT[i]), so old==0 every iteration and an
                                    // explicit changed=true would loop forever.
                                    // Line 1749 correctly compares against OUT[i].
                                }
                                // Propagate source-taint from src array to dst.
                                if (src_r < new_src_in.size()
                                    && new_src_in[src_r]
                                    && dst_r < new_src_out.size()) {
                                    new_src_out[dst_r] = 1;
                                    // Same reason: no explicit changed=true.
                                }
                                continue;
                            }
                            // AsyncTask.execute(params)/executeOnExecutor(exec,params):
                            // the framework internally invokes
                            // doInBackground(params) on the same receiver with
                            // the same array — but that call is dispatched by
                            // the framework at runtime, not by a bytecode
                            // invoke instruction, so the ordinary call graph
                            // never sees it. Model it directly: link the
                            // trailing array argument (and receiver) into the
                            // generic-erasure doInBackground bridge
                            // ([Ljava/lang/Object;)Ljava/lang/Object; — which
                            // for a Params type other than Object is a real
                            // compiled bridge method that itself invokes the
                            // typed doInBackground via an ordinary call (so no
                            // further special-casing is needed beyond this
                            // one hop), and for Params==Object is the real
                            // method directly.
                            if ((tgt.name == "execute"
                                 || tgt.name == "executeOnExecutor")
                                && !invoke->args.empty()) {
                                auto receiver_r = invoke->args[0];
                                auto array_r = invoke->args.back();
                                MethodId bridge_mid(
                                        tgt.type, "doInBackground",
                                        "([Ljava/lang/Object;)"
                                        "Ljava/lang/Object;");
                                auto bridge_mv =
                                        cg.method_vertices.find(bridge_mid);
                                if (bridge_mv != cg.method_vertices.end()
                                    && num_vertices(vm.methods()[bridge_mv
                                                                          ->second]
                                                             .insns)
                                               > 0) {
                                    CallContext bridge_ctx(2);
                                    CallContext bridge_src_ctx(2);
                                    if (receiver_r < new_in.size()
                                        && new_in[receiver_r].any()) {
                                        bridge_ctx.set(0);
                                    }
                                    if (array_r < new_in.size()
                                        && new_in[array_r].any()) {
                                        bridge_ctx.set(1);
                                    }
                                    if (receiver_r < new_src_in.size()
                                        && new_src_in[receiver_r]) {
                                        bridge_src_ctx.set(0);
                                    }
                                    if (array_r < new_src_in.size()
                                        && new_src_in[array_r]) {
                                        bridge_src_ctx.set(1);
                                    }
                                    get_or_compute_ctx(
                                            vm, bridge_mid, cg, bridge_ctx,
                                            bridge_src_ctx, cache, lib_policy,
                                            sinks, sink_hits, sources,
                                            source_sink_hits);

                                    // A field-taint variant of this bridge
                                    // call (threading this caller's
                                    // STATIC:/FIELD: src_field_taint entries
                                    // into doInBackground via a direct,
                                    // uncached compute_summary_ctx call, to
                                    // catch the "AsyncTask constructed with
                                    // empty Void params, reads a field set
                                    // before .execute()" pattern) was tried
                                    // and reverted: it caused real SIGSEGV
                                    // stack-overflow crashes on TaintBench
                                    // apps (hummingbad_android_samp.apk,
                                    // scipiex.apk, vibleaker_android_samp.apk)
                                    // because a direct compute_summary_ctx
                                    // call never registers bridge_mid in
                                    // cache.in_progress the way
                                    // get_or_compute_ctx does — so if
                                    // doInBackground itself contains another
                                    // .execute() call (directly or via a
                                    // helper), this recursed into itself with
                                    // no cycle guard at all, unlike every
                                    // other recursive path in this file. It
                                    // also measured zero net benefit on
                                    // TaintBench before being found unsafe.
                                    // See project memory
                                    // (taintbench-sweep-findings) before
                                    // reattempting; any retry needs the same
                                    // in_progress-style reentrancy guard
                                    // get_or_compute_ctx has, not just the
                                    // one-level "does the field set exist"
                                    // check this used.
                                }
                            }
                            MethodSummary callee_sum;
                            if (callee_ctx.none() && sources.empty()) {
                                // No tainted args and no source tracking —
                                // return cannot carry interesting taint.
                                callee_sum.param_count = invoke->args.size();
                                callee_sum.return_dep =
                                        DepSet(invoke->args.size());
                            } else {
                                // Look up or compute the summary.  When sources
                                // are configured we always run the callee even
                                // with an empty param-taint context so that
                                // src_return_dep is populated (source-taint is
                                // context-independent).
                                callee_sum = get_or_compute_ctx(
                                        vm, tgt, cg, callee_ctx,
                                        callee_src_ctx, cache,
                                        lib_policy, sinks, sink_hits,
                                        sources, source_sink_hits);
                            }

                            // Propagate return value taint.
                            for (std::size_t pi = 0;
                                 pi < callee_sum.return_dep.size(); ++pi) {
                                if (!callee_sum.return_dep.test(pi)) {
                                    continue;
                                }
                                if (pi < invoke->args.size()) {
                                    auto arg_reg = invoke->args[pi];
                                    if (arg_reg < new_in.size()) {
                                        new_pending |= new_in[arg_reg];
                                    }
                                }
                            }

                            // Propagate source-taint through callee return.
                            // Two cases:
                            // (A) The callee internally reaches a source API
                            //     and returns source-derived data regardless
                            //     of its arguments.
                            // (B) The callee's return depends on a parameter
                            //     that is source-tainted at this call site
                            //     (e.g. String.valueOf(tainted_double)).
                            //     Uses return_dep from the param-taint summary
                            //     to identify which params affect the return.
                            if (!src_callee_ret[i] && !sources.empty()) {
                                bool src_ret = callee_sum.src_return_dep;
                                if (!src_ret) {
                                    for (std::size_t pi = 0;
                                         pi < callee_sum.return_dep.size()
                                         && pi < invoke->args.size(); ++pi) {
                                        if (!callee_sum.return_dep.test(pi)) {
                                            continue;
                                        }
                                        auto arg_reg = invoke->args[pi];
                                        if (arg_reg < new_src_in.size()
                                            && new_src_in[arg_reg]) {
                                            src_ret = true;
                                            break;
                                        }
                                    }
                                }
                                if (src_ret) {
                                    src_callee_ret[i] = 1;
                                    // Capture origin: prefer the callee's own
                                    // src_return_origin if known.
                                    if (src_callee_origin[i].name.empty()
                                        && !callee_sum.src_return_origin.name
                                                .empty()) {
                                        src_callee_origin[i] =
                                                callee_sum.src_return_origin;
                                    }
                                    changed = true;
                                }
                            }

                            // Propagate callee field writes into the caller's
                            // field taint map (object-sensitive).
                            // Callee keys: "P{obj_pi}:{fkey}" or "STATIC:{fkey}"
                            // Caller keys: "R{args[obj_pi]}:{fkey}" or same static
                            for (const auto& kv : callee_sum.field_write_deps) {
                                if (kv.second.none()) {
                                    continue;
                                }
                                // Translate callee-param-indexed value taint
                                // to caller source params via actual arguments.
                                DepSet translated(sum.param_count);
                                for (std::size_t pi = 0;
                                     pi < kv.second.size()
                                     && pi < invoke->args.size(); ++pi) {
                                    if (!kv.second.test(pi)) {
                                        continue;
                                    }
                                    auto arg_reg = invoke->args[pi];
                                    if (arg_reg < new_in.size()) {
                                        translated |= new_in[arg_reg];
                                    }
                                }
                                if (!translated.any()) {
                                    continue;
                                }
                                // Map callee key to caller key.
                                std::string caller_key;
                                const auto& k = kv.first;
                                if (!k.empty() && k[0] == 'P') {
                                    // "P{obj_pi}:{fkey}" → "R{args[obj_pi]}:{fkey}"
                                    std::size_t obj_pi;
                                    std::string fkey;
                                    if (parse_indexed_field_key(k, obj_pi,
                                                                fkey)
                                        && obj_pi < invoke->args.size()) {
                                        caller_key =
                                                make_instance_field_taint_key(
                                                        invoke->args[obj_pi],
                                                        fkey);
                                    }
                                } else if (k.rfind("STATIC:", 0) == 0) {
                                    caller_key = k; // unchanged
                                }
                                if (!caller_key.empty()) {
                                    auto& ft = field_taint[caller_key];
                                    if (ft.size() < sum.param_count) {
                                        ft.resize(sum.param_count);
                                    }
                                    auto old_ft = ft;
                                    ft |= translated;
                                    if (ft != old_ft) {
                                        changed = true;
                                    }
                                }
                            }

                            // Source-taint through field_write_deps:
                            // If a callee writes a field with param P and
                            // the CALLER's actual arg for P is source-tainted,
                            // mark that field entry in src_field_taint.
                            // This handles the pattern: source-tainted arg
                            // passed to a setter (e.g. access$0) that stores
                            // it to a field; the caller can't see the iput
                            // but can see field_write_deps from the callee.
                            for (const auto& kv : callee_sum.field_write_deps) {
                                bool arg_src = false;
                                for (std::size_t pi = 0;
                                     pi < kv.second.size()
                                     && pi < invoke->args.size(); ++pi) {
                                    if (!kv.second.test(pi)) continue;
                                    auto arg_reg = invoke->args[pi];
                                    if (arg_reg < new_src_in.size()
                                        && new_src_in[arg_reg]) {
                                        arg_src = true;
                                        break;
                                    }
                                }
                                if (!arg_src) continue;
                                std::string sft_key;
                                const auto& k = kv.first;
                                if (!k.empty() && k[0] == 'P') {
                                    std::size_t obj_pi;
                                    std::string fkey;
                                    if (parse_indexed_field_key(k, obj_pi, fkey)
                                        && obj_pi < invoke->args.size()) {
                                        sft_key = make_instance_field_taint_key(
                                                invoke->args[obj_pi], fkey);
                                    }
                                } else if (k.rfind("STATIC:", 0) == 0) {
                                    sft_key = k;
                                }
                                if (!sft_key.empty()
                                    && src_field_taint.insert(sft_key).second) {
                                    changed = true;
                                }
                            }

                            // Propagate callee source_field_writes into the
                            // caller's src_field_taint so subsequent iget
                            // instructions can detect source-derived reads.
                            for (const auto& k : callee_sum.source_field_writes) {
                                std::string caller_sfw_key;
                                if (!k.empty() && k[0] == 'P') {
                                    std::size_t obj_pi;
                                    std::string sfw_fkey;
                                    if (parse_indexed_field_key(k, obj_pi,
                                                                sfw_fkey)
                                        && obj_pi < invoke->args.size()) {
                                        caller_sfw_key =
                                                make_instance_field_taint_key(
                                                        invoke->args[obj_pi],
                                                        sfw_fkey);
                                    }
                                } else if (k.rfind("STATIC:", 0) == 0
                                           || k.rfind("FIELD:", 0) == 0) {
                                    caller_sfw_key = k;
                                }
                                if (!caller_sfw_key.empty()) {
                                    if (src_field_taint
                                            .insert(caller_sfw_key)
                                            .second) {
                                        changed = true;
                                    }
                                }
                            }

                            // Static-field source propagation into callees:
                            // If src_field_taint has STATIC entries (e.g. a
                            // prior lifecycle method wrote source-tainted data
                            // to a static field), re-run concrete callees with
                            // those entries so source-to-sink flows that go
                            // through static fields across method boundaries
                            // are detected.  Only one level deep to bound cost;
                            // sub-callees still use cached summaries.
                            //
                            // This is a direct compute_summary_ctx call,
                            // bypassing get_or_compute_ctx — so unlike every
                            // other recursive path here, it does NOT
                            // automatically register itself in
                            // cache.in_progress/cache.call_stack. The
                            // !cache.in_progress.count(...) guard below only
                            // works if *something else* already marked this
                            // key in-progress; on its own this call is
                            // unguarded against reentrancy. Confirmed via a
                            // SIGSEGV stack-overflow crash on TaintBench apps
                            // (hummingbad_android_samp.apk, scipiex.apk,
                            // vibleaker_android_samp.apk — pre-existing, not
                            // introduced this session) where a callee reached
                            // this way itself contained a call back into the
                            // same probe pattern, recursing with no cycle
                            // check until the stack overflowed. Fixed by
                            // explicitly registering/unregistering in
                            // cache.in_progress and cache.call_stack around
                            // the call, matching what get_or_compute_ctx does
                            // — this makes both the in_progress guard AND the
                            // kMaxCallDepth cap in get_or_compute_ctx actually
                            // effective for this path too (call_stack depth
                            // accumulates correctly across nested probes).
                            if (!src_field_taint.empty()
                                && !cache.in_progress.count(
                                        CtxKey{tgt, callee_ctx,
                                               callee_src_ctx})) {
                                std::unordered_set<std::string> static_sft;
                                for (const auto& sk : src_field_taint) {
                                    if (sk.rfind("STATIC:", 0) == 0) {
                                        static_sft.insert(sk);
                                    }
                                }
                                if (!static_sft.empty()) {
                                    auto mv_callee =
                                            cg.method_vertices.find(tgt);
                                    if (mv_callee != cg.method_vertices.end()
                                        && num_vertices(
                                                   vm.methods()[mv_callee
                                                                        ->second]
                                                           .insns)
                                               > 0) {
                                        CtxKey probe_key{tgt, callee_ctx,
                                                         callee_src_ctx};
                                        cache.in_progress.insert(probe_key);
                                        cache.call_stack.push_back(probe_key);
                                        compute_summary_ctx(
                                                vm, tgt, mv_callee->second,
                                                cg, callee_ctx, callee_src_ctx,
                                                static_sft,
                                                cache, lib_policy, sinks,
                                                sink_hits, sources,
                                                source_sink_hits);
                                        cache.call_stack.pop_back();
                                        cache.in_progress.erase(probe_key);
                                    }
                                }
                            }
                        }
                    }
                    // Constructor receiver taint: when a library stub <init>
                    // is called with tainted args (1..n), propagate those
                    // taints to the receiver register (arg 0).  Models that
                    // constructing an object with tainted data makes the object
                    // a tainted carrier (e.g. RuntimeException(imei), PointF).
                    // Only applied with Conservative stub policy.
                    //
                    // NOTE: an earlier attempt widened this to ALSO cover
                    // void-returning instance mutators generally (setEntity,
                    // addHeader, add, put, ...), not just <init> — reasoning
                    // that e.g. httpPost.setEntity(taintedEntity) should make
                    // httpPost itself a tainted carrier. Reverted: it caused a
                    // real DroidBench regression (TP 130->126, Threading and
                    // EmulatorDetection lost previously-passing tests) — the
                    // broader trigger meaningfully increases per-call taint
                    // -propagation work, and some of that regression tracked
                    // with cases now hitting the compute-budget/inner-iteration
                    // safety valves that a narrower trigger wouldn't have hit.
                    // Left as a documented but NOT reattempted idea; see
                    // project memory.
                    if (invoke
                        && lib_policy == LibPolicy::Conservative
                        && invoke->callee.name == "<init>"
                        && invoke->args.size() >= 2) {
                        auto mv_chk = cg.method_vertices.find(invoke->callee);
                        bool is_stub_init =
                                (mv_chk == cg.method_vertices.end()
                                 || num_vertices(
                                        vm.methods()[mv_chk->second].insns)
                                    == 0);
                        if (is_stub_init) {
                            auto rcv_reg = invoke->args[0];
                            bool any_src_tainted = false;
                            for (std::size_t pi = 1;
                                 pi < invoke->args.size(); ++pi) {
                                auto arg_reg = invoke->args[pi];
                                if (arg_reg < new_in.size()
                                    && new_in[arg_reg].any()) {
                                    if (rcv_reg < new_out.size()) {
                                        new_out[rcv_reg] |= new_in[arg_reg];
                                    }
                                }
                                if (!any_src_tainted
                                    && arg_reg < new_src_in.size()
                                    && new_src_in[arg_reg]) {
                                    any_src_tainted = true;
                                }
                            }
                            if (any_src_tainted
                                && rcv_reg < new_src_out.size()
                                && !new_src_out[rcv_reg]) {
                                new_src_out[rcv_reg] = 1;
                            }
                        }
                    }
                    // StringBuilder/StringBuffer.append/insert receiver
                    // taint: sb.append(taintedValue) as a bare statement
                    // (return value unused, the overwhelmingly common way
                    // this API is called) has no move-result to carry the
                    // taint forward, so a later sb.toString() sees an
                    // untainted receiver even though every append() call
                    // leading up to it individually detected the appended
                    // value as tainted. Root-caused via TaintBench's
                    // roidsec.apk: getCallLogs() correctly marked each
                    // Cursor.getString() result and each append() call's
                    // (unused) return as tainted, but toString() came back
                    // untainted because sb itself was never contaminated.
                    // Deliberately much narrower than the reverted "all void
                    // mutators" attempt above (which regressed DroidBench):
                    // scoped to exactly these two well-known, ubiquitous
                    // fluent-builder classes rather than every stub call, to
                    // keep the added work — and thus safety-valve interaction
                    // risk — minimal.
                    else if (invoke
                             && lib_policy == LibPolicy::Conservative
                             && invoke->kind != InvokeKind::kStatic
                             && (invoke->callee.type.descriptor
                                         == "Ljava/lang/StringBuilder;"
                                 || invoke->callee.type.descriptor
                                            == "Ljava/lang/StringBuffer;")
                             && (invoke->callee.name == "append"
                                 || invoke->callee.name == "insert")
                             && invoke->args.size() >= 2) {
                        auto rcv_reg = invoke->args[0];
                        bool any_src_tainted = false;
                        for (std::size_t pi = 1; pi < invoke->args.size();
                             ++pi) {
                            auto arg_reg = invoke->args[pi];
                            if (arg_reg < new_in.size()
                                && new_in[arg_reg].any()
                                && rcv_reg < new_out.size()) {
                                new_out[rcv_reg] |= new_in[arg_reg];
                            }
                            if (arg_reg < new_src_in.size()
                                && new_src_in[arg_reg]) {
                                any_src_tainted = true;
                            }
                        }
                        if (any_src_tainted && rcv_reg < new_src_out.size()) {
                            new_src_out[rcv_reg] = 1;
                        }
                    }
                    // Apache HttpClient request-builder receiver taint:
                    // new HttpPost(url); post.setEntity(taintedEntity);
                    // client.execute(post); is a very common request-building
                    // pattern in older Android code (this library predates
                    // HttpURLConnection-based code in a lot of malware
                    // samples, including TaintBench's chulia.apk). setEntity
                    // is void-returning (no move-result to piggyback on,
                    // same fundamental issue as the StringBuilder case
                    // above, just without the fluent-chaining angle) and
                    // never marks its receiver (the request object) tainted
                    // on its own, so a later client.execute(post) sink check
                    // sees an untainted request even though the entity
                    // attached to it was tainted. Matched by method name +
                    // parameter type rather than a fixed list of concrete
                    // request classes (HttpPost, HttpPut, ..., all sharing
                    // this one HttpEntityEnclosingRequest-family method) —
                    // still narrow (name AND exact single-arg descriptor),
                    // not a general "any void call" trigger.
                    else if (invoke
                             && lib_policy == LibPolicy::Conservative
                             && invoke->kind != InvokeKind::kStatic
                             && invoke->callee.name == "setEntity"
                             && invoke->callee.descriptor
                                        == "(Lorg/apache/http/HttpEntity;)V"
                             && invoke->args.size() == 2) {
                        auto rcv_reg = invoke->args[0];
                        auto arg_reg = invoke->args[1];
                        if (arg_reg < new_in.size() && new_in[arg_reg].any()
                            && rcv_reg < new_out.size()) {
                            new_out[rcv_reg] |= new_in[arg_reg];
                        }
                        if (arg_reg < new_src_in.size()
                            && new_src_in[arg_reg]
                            && rcv_reg < new_src_out.size()) {
                            new_src_out[rcv_reg] = 1;
                        }
                    }
                }
                else if (opcode_val == opcode::op_move_result
                         || opcode_val == opcode::op_move_result_object
                         || opcode_val == opcode::op_move_result_wide) {
                    for (auto reg : DEF[i]) {
                        if (reg < new_out.size()) {
                            new_out[reg] = incoming;
                        }
                        // Source-taint: if predecessor was a source API call,
                        // mark this register as holding source-derived data.
                        if (reg < new_src_out.size()) {
                            new_src_out[reg] = src_incoming;
                        }
                        if (src_incoming && reg < src_origin.size()) {
                            src_origin[reg] = src_incoming_callee;
                        }
                    }
                }
                else if (opcode_val == opcode::op_move_exception) {
                    // Propagate taint from throw instructions that can reach
                    // this handler.  Two sources:
                    // (A) Direct CFG predecessors (explicit throw→catch edges).
                    // (B) Throw instructions within covering try ranges found
                    //     via the try-catch table (handles the common case where
                    //     no CFG edges were added from throw to catch handler).
                    // The full register state at each throw point flows into the
                    // catch block (all live registers remain in scope), while the
                    // exception-object DEF register gets only the thrown operand.
                    DepSet ex_dep(sum.param_count);
                    bool found_throw_pred = false;
                    for (auto ee = in_edges(v, ig);
                         ee.first != ee.second; ++ee.first) {
                        auto pred = source(*ee.first, ig);
                        if (pred >= index_of.size()) {
                            continue;
                        }
                        auto pred_idx = index_of[pred];
                        if (pred_idx >= n) {
                            continue;
                        }
                        const auto& pred_insn = ig[order[pred_idx]].insn;
                        if (op(pred_insn) != opcode::op_throw) {
                            continue;
                        }
                        found_throw_pred = true;
                        for (auto throw_reg : USE[pred_idx]) {
                            if (throw_reg < OUT[pred_idx].size()) {
                                ex_dep |= OUT[pred_idx][throw_reg];
                            }
                        }
                        for (auto throw_reg : USE[pred_idx]) {
                            if (throw_reg < SRC_OUT[pred_idx].size()
                                && SRC_OUT[pred_idx][throw_reg]) {
                                for (auto reg : DEF[i]) {
                                    if (reg < new_src_out.size()) {
                                        new_src_out[reg] = 1;
                                    }
                                }
                            }
                        }
                    }
                    if (!found_throw_pred) {
                        const auto& try_catches =
                                ig[boost::graph_bundle].try_catches;
                        for (const auto& tc : try_catches) {
                            bool is_handler =
                                    (tc.has_catch_all && tc.catch_all == v);
                            if (!is_handler) {
                                for (const auto& hdl : tc.hdls) {
                                    if (hdl.second == v) {
                                        is_handler = true;
                                        break;
                                    }
                                }
                            }
                            if (!is_handler) {
                                continue;
                            }
                            // Scan the try range for throw instructions.
                            for (auto vd = tc.first; vd <= tc.last; ++vd) {
                                if (vd >= index_of.size()) {
                                    continue;
                                }
                                auto throw_idx = index_of[vd];
                                if (throw_idx >= n) {
                                    continue;
                                }
                                if (op(ig[order[throw_idx]].insn)
                                    != opcode::op_throw) {
                                    continue;
                                }
                                // Join the full register state from the throw
                                // point so all live registers remain tainted.
                                for (std::size_t r = 0; r < reg_domain; ++r) {
                                    if (r < OUT[throw_idx].size()) {
                                        new_out[r] |= OUT[throw_idx][r];
                                    }
                                    if (r < SRC_OUT[throw_idx].size()) {
                                        new_src_out[r] |=
                                                SRC_OUT[throw_idx][r];
                                    }
                                }
                                // Accumulate thrown operand taint for DEF.
                                for (auto throw_reg : USE[throw_idx]) {
                                    if (throw_reg < OUT[throw_idx].size()) {
                                        ex_dep |= OUT[throw_idx][throw_reg];
                                    }
                                    // Mirror the DEF source-taint logic for
                                    // direct throw predecessors: if the thrown
                                    // register is source-tainted, the exception
                                    // object bound by move-exception is too.
                                    if (throw_reg < SRC_OUT[throw_idx].size()
                                        && SRC_OUT[throw_idx][throw_reg]) {
                                        for (auto reg : DEF[i]) {
                                            if (reg < new_src_out.size()) {
                                                new_src_out[reg] = 1;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                    for (auto reg : DEF[i]) {
                        if (reg < new_out.size()) {
                            new_out[reg] = ex_dep;
                        }
                    }
                }
                else if (opcode_val == opcode::op_return
                         || opcode_val == opcode::op_return_object
                         || opcode_val == opcode::op_return_wide) {
                    sum.return_dep |= use_dep;
                    // Propagate source-taint across method boundaries: if the
                    // return register holds source-API-derived data, mark this
                    // method as having a source-tainted return, and capture the
                    // best-effort source origin for downstream chain tracking.
                    for (auto reg : USE[i]) {
                        if (reg < new_src_in.size() && new_src_in[reg]) {
                            sum.src_return_dep = true;
                            if (sum.src_return_origin.name.empty()
                                && reg < src_origin.size()
                                && !src_origin[reg].name.empty()) {
                                sum.src_return_origin = src_origin[reg];
                            }
                        }
                    }
                }
                else if (is_iget(opcode_val) || is_sget(opcode_val)) {
                    // Field read: dest gets taint from any taint stored for
                    // this (object, field) pair, plus the object register's
                    // own taint (already in use_dep via USE[i]).
                    std::string fkey = get_field_key(vm, insn_obj);
                    DepSet field_dep(sum.param_count);
                    if (!fkey.empty()) {
                        std::string map_key;
                        if (is_iget(opcode_val)) {
                            // regs layout for iget: [dest, object].
                            // Skip dest (regs[0]) and take the object (regs[1]).
                            auto regs_view = regs(insn_obj);
                            auto rit = regs_view.begin();
                            if (rit != regs_view.end()) {
                                ++rit; // skip dest
                                if (rit != regs_view.end()) {
                                    std::size_t obj_idx;
                                    if (normalize_reg(*rit, reg_domain,
                                                      obj_idx)) {
                                        map_key = make_instance_field_taint_key(
                                                obj_idx, fkey);
                                    }
                                }
                            }
                        } else {
                            // sget: static field, no object register.
                            map_key = make_static_field_taint_key(fkey);
                        }
                        if (!map_key.empty()) {
                            auto it = field_taint.find(map_key);
                            if (it != field_taint.end()) {
                                field_dep = it->second;
                                if (field_dep.size() < sum.param_count) {
                                    field_dep.resize(sum.param_count);
                                }
                            }
                            // If a prior lifecycle callback (or callee) wrote
                            // source-API data to this field, mark dest as
                            // source-tainted too.  Check both the
                            // instance-specific key ("R{reg}:fkey") and the
                            // instance-insensitive key ("FIELD:fkey") so that
                            // inner-class → outer-class field writes that escape
                            // via FIELD: entries are picked up here.
                            if (src_field_taint.count(map_key)) {
                                for (auto reg : DEF[i]) {
                                    if (reg < new_src_out.size()) {
                                        new_src_out[reg] = 1;
                                    }
                                }
                            }
                            if (!fkey.empty()
                                && src_field_taint.count("FIELD:" + fkey)) {
                                for (auto reg : DEF[i]) {
                                    if (reg < new_src_out.size()) {
                                        new_src_out[reg] = 1;
                                    }
                                }
                            }
                        }
                    }
                    for (auto reg : DEF[i]) {
                        if (reg < new_out.size()) {
                            // Field-sensitive: the VALUE of a field is
                            // independent of the taint on the object reference.
                            // Using 'use_dep | field_dep' would propagate the
                            // pointer's own taint (e.g. 'this') to every field
                            // read, causing false positives.  Only field_dep.
                            new_out[reg] = field_dep;
                        }
                    }
                }
                else if (is_iput(opcode_val) || is_sput(opcode_val)) {
                    // Field write: taint from VALUE register flows into the
                    // (object, field) slot in field_taint.
                    // iput layout: regs[0]=value, regs[1]=object.
                    // sput layout: regs[0]=value (no object register).
                    std::string fkey = get_field_key(vm, insn_obj);
                    if (!fkey.empty()) {
                        auto regs_view = regs(insn_obj);
                        auto rit = regs_view.begin();
                        if (rit != regs_view.end()) {
                            std::size_t val_idx;
                            if (normalize_reg(*rit, reg_domain, val_idx)
                                && val_idx < new_in.size()) {
                                // Compute map_key regardless of taint so we
                                // can kill the field entry on untainted writes.
                                std::string map_key;
                                if (is_iput(opcode_val)) {
                                    // Advance to object register (regs[1]).
                                    ++rit;
                                    if (rit != regs_view.end()) {
                                        std::size_t obj_idx;
                                        if (normalize_reg(*rit, reg_domain,
                                                          obj_idx)) {
                                            map_key =
                                                    make_instance_field_taint_key(
                                                            obj_idx, fkey);
                                        }
                                    }
                                } else {
                                    // sput: static field.
                                    map_key = make_static_field_taint_key(fkey);
                                }
                                if (!map_key.empty()) {
                                    if (new_in[val_idx].any()) {
                                        auto& ft = field_taint[map_key];
                                        if (ft.size() < sum.param_count) {
                                            ft.resize(sum.param_count);
                                        }
                                        auto old_ft = ft;
                                        ft |= new_in[val_idx];
                                        // Wide value (long/double) spans
                                        // val_idx and val_idx+1; include
                                        // the high word's taint.
                                        if ((opcode_val == opcode::op_iput_wide
                                             || opcode_val
                                                        == opcode::op_sput_wide)
                                            && val_idx + 1 < new_in.size()) {
                                            ft |= new_in[val_idx + 1];
                                        }
                                        if (ft != old_ft) {
                                            changed = true;
                                        }
                                    } else {
                                        // Kill: writing an untainted constant
                                        // to a field erases prior taint so
                                        // we do not report false positives
                                        // for constant-overwrite patterns.
                                        auto it = field_taint.find(map_key);
                                        if (it != field_taint.end()
                                            && it->second.any()) {
                                            it->second.reset();
                                            changed = true;
                                        }
                                    }
                                    // Track source-API-derived writes: if the
                                    // value register carries source taint, record
                                    // this field so later iget reads can pick it up
                                    // (intra-method) or the summary can export it
                                    // (cross-lifecycle / cross-callee).
                                    bool val_src = (val_idx < new_src_in.size()
                                                    && new_src_in[val_idx]);
                                    if (!val_src
                                        && (opcode_val == opcode::op_iput_wide
                                            || opcode_val == opcode::op_sput_wide)
                                        && val_idx + 1 < new_src_in.size()) {
                                        val_src = new_src_in[val_idx + 1];
                                    }
                                    if (val_src) {
                                        if (src_field_taint.insert(map_key)
                                                .second) {
                                            changed = true;
                                        }
                                    }
                                }
                            }
                        }
                    }
                    // iput/sput have no register defs; new_out is unchanged.
                }
                else if (is_aget(opcode_val)) {
                    // Array load: vA = vB[vC].
                    // Taint of vA = element taint accumulated by prior aputs
                    // for this array register, OR the array reference's own
                    // taint (handles filled-new-array results and tainted param
                    // arrays).  Index taint (vC) is intentionally not propagated.
                    DepSet array_dep(sum.param_count);
                    auto regs_view = regs(insn_obj);
                    auto rit = regs_view.begin();
                    if (rit != regs_view.end()) {
                        ++rit; // skip dest (vA), advance to array register (vB)
                        if (rit != regs_view.end()) {
                            std::size_t arr_idx;
                            if (normalize_reg(*rit, reg_domain, arr_idx)) {
                                auto arr_key = make_instance_field_taint_key(
                                        arr_idx, "[]");
                                auto it = field_taint.find(arr_key);
                                if (it != field_taint.end()) {
                                    array_dep = it->second;
                                    if (array_dep.size() < sum.param_count) {
                                        array_dep.resize(sum.param_count);
                                    }
                                }
                                // Also include array-reference taint (covers
                                // arrays created by filled-new-array or
                                // received as tainted parameters).
                                if (arr_idx < new_in.size()) {
                                    array_dep |= new_in[arr_idx];
                                }
                            }
                        }
                    }
                    for (auto reg : DEF[i]) {
                        if (reg < new_out.size()) {
                            new_out[reg] = array_dep;
                        }
                    }
                }
                else if (is_aput(opcode_val)) {
                    // Array store: vB[vC] = vA.
                    // Param-taint of the value (vA) flows into the element
                    // taint slot for array register vB.
                    // Source-taint from vA is also propagated to the vB
                    // register so that Method.invoke(recv, args) detects
                    // tainted elements when args is checked in maybe_report_*.
                    auto regs_view = regs(insn_obj);
                    auto rit = regs_view.begin();
                    if (rit != regs_view.end()) {
                        std::size_t val_idx;
                        if (normalize_reg(*rit, reg_domain, val_idx)) {
                            DepSet val_dep(sum.param_count);
                            if (val_idx < new_in.size()) {
                                val_dep |= new_in[val_idx];
                            }
                            if (opcode_val == opcode::op_aput_wide
                                && val_idx + 1 < new_in.size()) {
                                val_dep |= new_in[val_idx + 1];
                            }
                            bool val_src = (val_idx < new_src_in.size()
                                            && new_src_in[val_idx]);
                            if (!val_src && opcode_val == opcode::op_aput_wide
                                && val_idx + 1 < new_src_in.size()) {
                                val_src = new_src_in[val_idx + 1];
                            }
                            if (val_dep.any() || val_src) {
                                ++rit; // advance to array register (vB)
                                if (rit != regs_view.end()) {
                                    std::size_t arr_idx;
                                    if (normalize_reg(*rit, reg_domain,
                                                      arr_idx)) {
                                        if (val_dep.any()) {
                                            auto arr_key =
                                                    make_instance_field_taint_key(
                                                            arr_idx, "[]");
                                            auto& ft = field_taint[arr_key];
                                            if (ft.size() < sum.param_count) {
                                                ft.resize(sum.param_count);
                                            }
                                            auto old_ft = ft;
                                            ft |= val_dep;
                                            if (ft != old_ft) {
                                                changed = true;
                                            }
                                        }
                                        // Propagate source-taint from element
                                        // to the array register itself so that
                                        // the args array passed to Method.invoke
                                        // carries source taint.
                                        if (val_src
                                            && arr_idx < new_src_out.size()
                                            && !new_src_out[arr_idx]) {
                                            new_src_out[arr_idx] = 1;
                                        }
                                    }
                                }
                            }
                        }
                    }
                    // aput has no register def; new_out is unchanged.
                }
                else if (opcode_val == opcode::op_filled_new_array
                         || opcode_val
                                    == opcode::op_filled_new_array_range) {
                    // Creates an array whose elements are the argument
                    // registers.  Propagate the union of element taints via
                    // new_pending so that the following move-result-object
                    // marks the array reference as tainted.
                    new_pending = use_dep;
                }
                else {
                    for (auto reg : DEF[i]) {
                        if (reg < new_out.size()) {
                            new_out[reg] = use_dep;
                        }
                    }
                }

                // General source-taint use→def propagation (covers all
                // instructions that aren't invoke or move-result).
                if (!info(opcode_val).can_invoke()
                    && opcode_val != opcode::op_move_result
                    && opcode_val != opcode::op_move_result_object
                    && opcode_val != opcode::op_move_result_wide) {
                    uint8_t src_use = 0;
                    MethodId src_use_origin;
                    for (auto reg : USE[i]) {
                        if (reg < new_src_in.size() && new_src_in[reg]) {
                            src_use = 1;
                            if (reg < src_origin.size()) {
                                src_use_origin = src_origin[reg];
                            }
                            break;
                        }
                    }
                    if (src_use) {
                        for (auto reg : DEF[i]) {
                            if (reg < new_src_out.size()) {
                                new_src_out[reg] = 1;
                                if (reg < src_origin.size()
                                    && src_origin[reg].name.empty()) {
                                    src_origin[reg] = src_use_origin;
                                }
                            }
                        }
                    }
                }

                // At the method entry (no-predecessor instruction), the param
                // registers are "defined" by a synthetic binding instruction.
                // That DEF kill removes the param_seed taint we set in new_in.
                // Restore it: the analysis models parameters as tainted at entry,
                // so OR param_seed back into new_out unconditionally.
                if (!saw_pred) {
                    for (std::size_t r = 0; r < reg_domain; ++r) {
                        new_out[r] |= param_seed[r];
                        if (src_param_seed[r]) {
                            new_src_out[r] = 1;
                        }
                    }
                }

                if (new_in != IN[i] || new_out != OUT[i]
                    || new_pending != pending[i]
                    || new_src_out != SRC_OUT[i]) {
                    IN[i] = std::move(new_in);
                    OUT[i] = std::move(new_out);
                    pending[i] = std::move(new_pending);
                    SRC_OUT[i] = std::move(new_src_out);
                    changed = true;
                }
            }
        }
        // Export accumulated field writes so callers can propagate field taint
        // across method boundaries.  Convert register-indexed intra-method keys
        // "R{reg}:{fkey}" to parameter-indexed inter-method keys "P{param}:{fkey}"
        // (only for object registers that correspond to parameters of this method).
        // Fields written through local (non-parameter) object registers are not
        // observable from callers and are dropped.  Static fields "STATIC:{fkey}"
        // are exported as-is.
        {
            const auto param_start = (sum.param_count <= reg_domain)
                                     ? (reg_domain - sum.param_count) : 0;
            for (const auto& kv : field_taint) {
                if (kv.second.none()) {
                    continue;
                }
                const auto& k = kv.first;
                if (k.rfind("STATIC:", 0) == 0) {
                    sum.field_write_deps[k] = kv.second;
                } else if (!k.empty() && k[0] == 'R') {
                    std::size_t reg_idx;
                    std::string fkey;
                    if (parse_indexed_field_key(k, reg_idx, fkey)
                        && reg_idx >= param_start && reg_idx < reg_domain) {
                        std::size_t param_idx = reg_idx - param_start;
                        sum.field_write_deps[make_field_write_key(param_idx,
                                                                   fkey)] =
                                kv.second;
                    }
                }
            }
        }
        // Export source_field_writes: convert src_field_taint register-indexed
        // keys to param-indexed inter-method keys, mirroring field_write_deps.
        // Used by the lifecycle pass and callee propagation logic.
        {
            const auto param_start = (sum.param_count <= reg_domain)
                                     ? (reg_domain - sum.param_count) : 0;
            for (const auto& k : src_field_taint) {
                if (k.rfind("STATIC:", 0) == 0
                    || k.rfind("FIELD:", 0) == 0) {
                    sum.source_field_writes.insert(k);
                } else if (!k.empty() && k[0] == 'R') {
                    std::size_t reg_idx;
                    std::string fkey;
                    if (parse_indexed_field_key(k, reg_idx, fkey)) {
                        if (reg_idx >= param_start && reg_idx < reg_domain) {
                            std::size_t param_idx = reg_idx - param_start;
                            sum.source_field_writes.insert(
                                    make_field_write_key(param_idx, fkey));
                        } else {
                            // Non-param instance write (e.g. inner class writing
                            // an outer-class field via a captured this$0 ref).
                            // Export as instance-insensitive "FIELD:" key so the
                            // lifecycle pass can propagate the taint across the
                            // callback → component boundary.
                            sum.source_field_writes.insert("FIELD:" + fkey);
                        }
                    }
                }
            }
        }
        return sum;
    }

    // Demand-driven, memoized entry point for context-sensitive summaries.
    //
    // Uses optimistic fixed-point iteration to handle recursive and mutually
    // recursive calls precisely:
    //   - Recursive calls receive an optimistic (empty) stub initially.
    //   - After each iteration the interim is updated; stale callee entries
    //     are evicted so they are re-analysed with the updated interim.
    //   - Iteration stops when the summary no longer changes (fixed point).
    // DepSets grow monotonically, so convergence is guaranteed by the finite
    // lattice height (2^param_count).
    static MethodSummary get_or_compute_ctx(
            virtual_machine& vm,
            const MethodId& mid,
            const CallGraph& cg,
            const CallContext& ctx,
            const CallContext& src_ctx,
            CtxCache& cache,
            LibPolicy lib_policy,
            const std::vector<SinkSpec>& sinks,
            std::vector<SinkHit>& sink_hits,
            const std::vector<SourceSpec>& sources,
            std::vector<SourceHit>& source_sink_hits)
    {
        CtxKey key{mid, ctx, src_ctx};

        // Already computed?
        {
            auto it = cache.summaries.find(key);
            if (it != cache.summaries.end()) {
                return it->second;
            }
        }

        // Recursive call: return best known optimistic summary (bottom = empty).
        if (cache.in_progress.count(key)) {
            auto it = cache.interim.find(key);
            if (it != cache.interim.end()) {
                return it->second;
            }
            MethodSummary opt;
            opt.param_count = ctx.size();
            opt.return_dep = DepSet(ctx.size());
            return opt;
        }

        // No code available (library/native method)? Return a stub.
        auto mv_it = cg.method_vertices.find(mid);
        if (mv_it == cg.method_vertices.end()
            || num_vertices(vm.methods()[mv_it->second].insns) == 0) {
            return stub_summary(ctx.size(), lib_policy);
        }

        // Work budget exhausted (see CtxCache::compute_calls) — don't start a
        // fresh analysis; fall back to the same conservative stub already
        // used for unmodeled library methods rather than continuing to feed
        // a runaway cache-eviction cascade.
        if (cache.compute_calls >= CtxCache::kComputeBudget) {
            return stub_summary(ctx.size(), lib_policy);
        }

        // Recursion-depth cap: get_or_compute_ctx and compute_summary_ctx
        // are mutually recursive with no separate bound on call *depth*
        // (kComputeBudget bounds total work across a whole seed, not how
        // deep a single chain of calls can nest). Observed crashing with
        // SIGSEGV (stack overflow) on real-world APKs
        // (hummingbad_android_samp.apk) at ~2960 nested frames of
        // get_or_compute_ctx<->compute_summary_ctx from a single top-level
        // seed — no cycle for cache.in_progress to catch, just a very deep
        // (or effectively unbounded, e.g. from a long synthetic AsyncTask
        // bridge / one-level-deep-probe chain) acyclic call chain. 300 is
        // far above any legitimate call depth seen in DroidBench or the
        // TaintBench corpus but far below the depth that actually
        // overflows the stack, so this should only trip on genuine
        // pathological chains.
        static constexpr std::size_t kMaxCallDepth = 300;
        if (cache.call_stack.size() >= kMaxCallDepth) {
            return stub_summary(ctx.size(), lib_policy);
        }

        // Seed interim at bottom of lattice (optimistic: assume no taint).
        {
            MethodSummary opt;
            opt.param_count = ctx.size();
            opt.return_dep = DepSet(ctx.size());
            cache.interim.emplace(key, std::move(opt));
        }
        cache.in_progress.insert(key);
        cache.call_stack.push_back(key);

        // Fixed-point iteration.  DepSets only grow, so this always terminates.
        MethodSummary sum;
        static constexpr int MAX_ITER = 16;
        for (int iter = 0; iter < MAX_ITER; ++iter) {
            sum = compute_summary_ctx(vm, mid, mv_it->second, cg, ctx,
                                      src_ctx,
                                      /*pre_src_field_taint=*/{},
                                      cache, lib_policy, sinks, sink_hits,
                                      sources, source_sink_hits);
            const auto& prev = cache.interim.at(key);
            const bool converged =
                    (prev.return_dep == sum.return_dep
                     && prev.field_write_deps == sum.field_write_deps
                     && prev.source_field_writes == sum.source_field_writes);
            if (converged) {
                break;
            }
            // Interim changed: evict callee summaries computed with the old
            // interim so they will be re-analysed in the next iteration.
            for (const auto& stale : cache.added_during[key]) {
                cache.summaries.erase(stale);
            }
            cache.added_during[key].clear();
            cache.interim.at(key) = sum;
        }

        cache.call_stack.pop_back();
        cache.in_progress.erase(key);
        cache.interim.erase(key);
        cache.added_during.erase(key);

        // Register this result with the enclosing analysis so it can be
        // evicted if the enclosing method's interim changes.
        if (!cache.call_stack.empty()) {
            cache.added_during[cache.call_stack.back()].push_back(key);
        }
        cache.summaries.emplace(key, sum);
        return sum;
    }

} // namespace

MethodId::MethodId(jvm_type_hdl type, std::string name, std::string descriptor)
        : type(type), name(std::move(name)), descriptor(std::move(descriptor))
{
}

std::size_t MethodIdHash::operator()(const MethodId& id) const
{
    std::size_t h1 = hash_value(id.type);
    std::size_t h2 = std::hash<std::string>()(id.name);
    std::size_t h3 = std::hash<std::string>()(id.descriptor);
    return h1 ^ (h2 << 1) ^ (h3 << 2);
}

bool operator==(const MethodId& a, const MethodId& b)
{
    return a.type == b.type && a.name == b.name && a.descriptor == b.descriptor;
}

bool operator!=(const MethodId& a, const MethodId& b)
{
    return !(a == b);
}

std::size_t CallSiteIdHash::operator()(const CallSiteId& cs) const
{
    std::size_t h1 = MethodIdHash{}(cs.caller);
    std::size_t h2 = std::hash<uint32_t>()(cs.offset);
    return h1 ^ (h2 << 1);
}

bool operator==(const CallSiteId& a, const CallSiteId& b)
{
    return a.caller == b.caller && a.offset == b.offset;
}

MethodId make_method_id(const jvm_method_hdl& hdl)
{
    return make_method_id_local(hdl);
}

namespace {
    // One entry in a lifecycle method sequence table.
    struct LifecycleEntry {
        const char* name;
        const char* descriptor;
        int order;
    };

    // Standard Android Activity lifecycle, including common override points.
    static const LifecycleEntry kActivityLifecycle[] = {
        {"<init>",                  "()V",                                           0},
        {"onCreate",                "(Landroid/os/Bundle;)V",                        1},
        {"onStart",                 "()V",                                           2},
        {"onRestoreInstanceState",  "(Landroid/os/Bundle;)V",                        3},
        {"onResume",                "()V",                                           4},
        {"onNewIntent",             "(Landroid/content/Intent;)V",                   5},
        {"onActivityResult",        "(IILandroid/content/Intent;)V",                 6},
        {"onPause",                 "()V",                                           7},
        {"onSaveInstanceState",     "(Landroid/os/Bundle;)V",                        8},
        {"onStop",                  "()V",                                           9},
        {"onRestart",               "()V",                                          10},
        {"onDestroy",               "()V",                                          11},
    };
    static constexpr std::size_t kActivityLifecycleLen =
            sizeof(kActivityLifecycle) / sizeof(kActivityLifecycle[0]);

    static const LifecycleEntry kServiceLifecycle[] = {
        {"<init>",          "()V",                                          0},
        {"onCreate",        "()V",                                          1},
        {"onStartCommand",  "(Landroid/content/Intent;II)I",                2},
        {"onBind",          "(Landroid/content/Intent;)Landroid/os/IBinder;", 3},
        {"onUnbind",        "(Landroid/content/Intent;)Z",                  4},
        {"onDestroy",       "()V",                                          5},
        {"onLowMemory",     "()V",                                          6},
        {"onTrimMemory",    "(I)V",                                         7},
    };
    static constexpr std::size_t kServiceLifecycleLen =
            sizeof(kServiceLifecycle) / sizeof(kServiceLifecycle[0]);

    static const LifecycleEntry kReceiverLifecycle[] = {
        {"onReceive",
         "(Landroid/content/Context;Landroid/content/Intent;)V",
         0},
    };
    static constexpr std::size_t kReceiverLifecycleLen =
            sizeof(kReceiverLifecycle) / sizeof(kReceiverLifecycle[0]);

    static const LifecycleEntry kProviderLifecycle[] = {
        {"onCreate",  "()Z",                                                0},
        {"query",
         "(Landroid/net/Uri;[Ljava/lang/String;Ljava/lang/String;"
         "[Ljava/lang/String;Ljava/lang/String;)Landroid/database/Cursor;",
         1},
        {"insert",
         "(Landroid/net/Uri;Landroid/content/ContentValues;)"
         "Landroid/net/Uri;",
         2},
        {"update",
         "(Landroid/net/Uri;Landroid/content/ContentValues;"
         "Ljava/lang/String;[Ljava/lang/String;)I",
         3},
        {"delete",
         "(Landroid/net/Uri;Ljava/lang/String;[Ljava/lang/String;)I",
         4},
    };
    static constexpr std::size_t kProviderLifecycleLen =
            sizeof(kProviderLifecycle) / sizeof(kProviderLifecycle[0]);

    // Also treat Application and Fragment as mini-lifecycles.
    static const LifecycleEntry kApplicationLifecycle[] = {
        {"onCreate",        "()V",  0},
        {"onLowMemory",     "()V",  1},
        {"onTrimMemory",    "(I)V", 2},
        {"onTerminate",     "()V",  3},
    };
    static constexpr std::size_t kApplicationLifecycleLen =
            sizeof(kApplicationLifecycle) / sizeof(kApplicationLifecycle[0]);

    // android.view.View.OnClickListener — fired when a View is clicked.
    static const LifecycleEntry kOnClickListenerMethods[] = {
        {"onClick", "(Landroid/view/View;)V", 0},
    };
    static constexpr std::size_t kOnClickListenerMethodsLen =
            sizeof(kOnClickListenerMethods) / sizeof(kOnClickListenerMethods[0]);

    // android.location.LocationListener — fired by LocationManager callbacks.
    static const LifecycleEntry kLocationListenerMethods[] = {
        {"onLocationChanged", "(Landroid/location/Location;)V",            0},
        {"onStatusChanged",   "(Ljava/lang/String;ILandroid/os/Bundle;)V", 1},
        {"onProviderEnabled", "(Ljava/lang/String;)V",                     2},
        {"onProviderDisabled","(Ljava/lang/String;)V",                     3},
    };
    static constexpr std::size_t kLocationListenerMethodsLen =
            sizeof(kLocationListenerMethods) / sizeof(kLocationListenerMethods[0]);

    // android.app.Application.ActivityLifecycleCallbacks — global activity
    // lifecycle events registered via Application.registerActivityLifecycleCallbacks.
    static const LifecycleEntry kActivityLifecycleCallbacksMethods[] = {
        {"onActivityCreated",           "(Landroid/app/Activity;Landroid/os/Bundle;)V", 0},
        {"onActivityStarted",           "(Landroid/app/Activity;)V",                    1},
        {"onActivityResumed",           "(Landroid/app/Activity;)V",                    2},
        {"onActivityPaused",            "(Landroid/app/Activity;)V",                    3},
        {"onActivityStopped",           "(Landroid/app/Activity;)V",                    4},
        {"onActivitySaveInstanceState", "(Landroid/app/Activity;Landroid/os/Bundle;)V", 5},
        {"onActivityDestroyed",         "(Landroid/app/Activity;)V",                    6},
    };
    static constexpr std::size_t kActivityLifecycleCallbacksMethodsLen =
            sizeof(kActivityLifecycleCallbacksMethods)
            / sizeof(kActivityLifecycleCallbacksMethods[0]);

    // android.content.ComponentCallbacks2 — registered via Context.registerComponentCallbacks.
    static const LifecycleEntry kComponentCallbacks2Methods[] = {
        {"onLowMemory",            "()V",                                                0},
        {"onConfigurationChanged", "(Landroid/content/res/Configuration;)V",             1},
        {"onTrimMemory",           "(I)V",                                               2},
    };
    static constexpr std::size_t kComponentCallbacks2MethodsLen =
            sizeof(kComponentCallbacks2Methods)
            / sizeof(kComponentCallbacks2Methods[0]);

    // android.view.View — custom View subclasses with drawing/layout callbacks.
    // Seeded in Phase 2b so static fields written during Activity.onCreate
    // (e.g. MyView.deviceID = getDeviceId()) are visible to onDraw.
    static const LifecycleEntry kViewMethods[] = {
        {"onDraw",    "(Landroid/graphics/Canvas;)V", 0},
        {"onMeasure", "(II)V",                        1},
        {"onLayout",  "(ZIIII)V",                     2},
    };
    static constexpr std::size_t kViewMethodsLen =
            sizeof(kViewMethods) / sizeof(kViewMethods[0]);

    // Component type descriptor → (table, length) for lifecycle ordering.
    // always_run=true: run even with a single method (callback interfaces that
    // are always invoked by the framework regardless of intra-component ordering).
    struct ComponentLifecycleTable {
        const char* base_descriptor;
        const LifecycleEntry* entries;
        std::size_t len;
        bool always_run;
    };
    static const ComponentLifecycleTable kComponentLifecycles[] = {
        {"Landroid/app/Activity;",              kActivityLifecycle,       kActivityLifecycleLen,       false},
        {"Landroid/app/Service;",               kServiceLifecycle,        kServiceLifecycleLen,        false},
        {"Landroid/content/BroadcastReceiver;", kReceiverLifecycle,       kReceiverLifecycleLen,       false},
        {"Landroid/content/ContentProvider;",   kProviderLifecycle,       kProviderLifecycleLen,       false},
        {"Landroid/app/Application;",           kApplicationLifecycle,    kApplicationLifecycleLen,    false},
        {"Landroid/view/View;",                 kViewMethods,             kViewMethodsLen,             false},
        {"Landroid/view/View$OnClickListener;",                    kOnClickListenerMethods,            kOnClickListenerMethodsLen,            true},
        {"Landroid/location/LocationListener;",                    kLocationListenerMethods,           kLocationListenerMethodsLen,           true},
        {"Landroid/app/Application$ActivityLifecycleCallbacks;",   kActivityLifecycleCallbacksMethods, kActivityLifecycleCallbacksMethodsLen, true},
        {"Landroid/content/ComponentCallbacks2;",                  kComponentCallbacks2Methods,        kComponentCallbacks2MethodsLen,        true},
    };
    static constexpr std::size_t kComponentLifecyclesLen =
            sizeof(kComponentLifecycles) / sizeof(kComponentLifecycles[0]);

    std::vector<SinkSpec> default_sinks()
    {
        return {
                // -------------------------------------------------------
                // Command execution
                // -------------------------------------------------------
                {"Ljava/lang/Runtime;", "exec",
                 "(Ljava/lang/String;)Ljava/lang/Process;"},
                {"Ljava/lang/Runtime;", "exec",
                 "([Ljava/lang/String;)Ljava/lang/Process;"},
                {"Ljava/lang/ProcessBuilder;", "<init>",
                 "([Ljava/lang/String;)V"},
                {"Ljava/lang/ProcessBuilder;", "<init>",
                 "(Ljava/util/List;)V"},
                {"Ljava/lang/ProcessBuilder;", "start",
                 "()Ljava/lang/Process;"},

                // -------------------------------------------------------
                // File I/O — tainted file path or data written/read
                // -------------------------------------------------------
                {"Ljava/io/FileOutputStream;", "<init>",
                 "(Ljava/lang/String;)V"},
                {"Ljava/io/FileOutputStream;", "<init>",
                 "(Ljava/lang/String;Z)V"},
                {"Ljava/io/FileWriter;", "<init>",
                 "(Ljava/lang/String;)V"},
                {"Ljava/io/FileWriter;", "<init>",
                 "(Ljava/lang/String;Z)V"},
                {"Ljava/io/FileInputStream;", "<init>",
                 "(Ljava/lang/String;)V"},
                {"Ljava/io/RandomAccessFile;", "<init>",
                 "(Ljava/lang/String;Ljava/lang/String;)V"},
                {"Ljava/io/File;", "delete", "()Z"},
                // OutputStream.write — low-level byte/stream write
                {"Ljava/io/OutputStream;", "write", "([B)V"},
                {"Ljava/io/OutputStream;", "write", "([BII)V"},
                {"Ljava/io/OutputStream;", "write", "(I)V"},
                // Writer.write — character/string stream write
                {"Ljava/io/Writer;", "write", "([C)V"},
                {"Ljava/io/Writer;", "write", "([CII)V"},
                {"Ljava/io/Writer;", "write", "(I)V"},
                {"Ljava/io/Writer;", "write", "(Ljava/lang/String;)V"},
                {"Ljava/io/Writer;", "write", "(Ljava/lang/String;II)V"},
                {"Ljava/io/Writer;", "append",
                 "(Ljava/lang/CharSequence;)Ljava/io/Writer;"},
                {"Ljava/io/OutputStreamWriter;", "append",
                 "(Ljava/lang/CharSequence;)Ljava/io/Writer;"},
                // DataOutputStream's own byte/UTF-string write overloads —
                // same family as the generic OutputStream.write above.
                {"Ljava/io/DataOutputStream;", "writeBytes",
                 "(Ljava/lang/String;)V"},
                {"Ljava/io/DataOutputStream;", "writeUTF",
                 "(Ljava/lang/String;)V"},
                // flush() takes no data argument of its own, but if the
                // stream object itself already carries taint (e.g. from a
                // preceding tainted .write() call — see the receiver
                // contamination in maybe_report_source_sink) a later
                // flush() on that same object is also a source-to-sink hit.
                {"Ljava/io/OutputStream;", "flush", "()V"},
                {"Ljava/io/Writer;", "flush", "()V"},

                // -------------------------------------------------------
                // Network — tainted URL / hostname / port / socket
                // -------------------------------------------------------
                {"Ljava/net/URL;", "<init>",
                 "(Ljava/lang/String;)V"},
                {"Ljava/net/URL;", "set",
                 "(Ljava/lang/String;Ljava/lang/String;I"
                 "Ljava/lang/String;Ljava/lang/String;)V"},
                {"Ljava/net/URL;", "set",
                 "(Ljava/lang/String;Ljava/lang/String;I"
                 "Ljava/lang/String;Ljava/lang/String;"
                 "Ljava/lang/String;Ljava/lang/String;Ljava/lang/String;)V"},
                {"Ljava/net/Socket;", "<init>",
                 "(Ljava/lang/String;I)V"},
                {"Ljava/net/Socket;", "connect",
                 "(Ljava/net/SocketAddress;)V"},
                {"Ljava/net/URLConnection;", "connect", "()V"},
                {"Ljava/net/URLConnection;", "getOutputStream",
                 "()Ljava/io/OutputStream;"},
                // getInputStream is also a source (response body), but the
                // *call itself* is what actually sends a request whose URL
                // may carry tainted data embedded as query params (GET-based
                // exfiltration, as opposed to getOutputStream's POST body) —
                // so it's listed as a sink too, matching how it's used across
                // several TaintBench samples.
                {"Ljava/net/URLConnection;", "getInputStream",
                 "()Ljava/io/InputStream;"},
                {"Ljava/net/HttpURLConnection;", "getInputStream",
                 "()Ljava/io/InputStream;"},
                {"Lorg/apache/http/impl/client/DefaultHttpClient;",
                 "execute",
                 "(Lorg/apache/http/client/methods/HttpUriRequest;)"
                 "Lorg/apache/http/HttpResponse;"},
                {"Lorg/apache/http/client/HttpClient;",
                 "execute",
                 "(Lorg/apache/http/client/methods/HttpUriRequest;)"
                 "Lorg/apache/http/HttpResponse;"},
                // Spring RestTemplate — common in a handful of samples as an
                // alternative REST client to HttpClient/HttpURLConnection.
                {"Lorg/springframework/web/client/RestTemplate;", "exchange",
                 "(Ljava/lang/String;Lorg/springframework/http/HttpMethod;"
                 "Lorg/springframework/http/HttpEntity;Ljava/lang/Class;"
                 "[Ljava/lang/Object;)"
                 "Lorg/springframework/http/ResponseEntity;"},

                // -------------------------------------------------------
                // Android logging — information disclosure via logcat
                // -------------------------------------------------------
                {"Landroid/util/Log;", "v",
                 "(Ljava/lang/String;Ljava/lang/String;)I"},
                {"Landroid/util/Log;", "v",
                 "(Ljava/lang/String;Ljava/lang/String;Ljava/lang/Throwable;)I"},
                {"Landroid/util/Log;", "d",
                 "(Ljava/lang/String;Ljava/lang/String;)I"},
                {"Landroid/util/Log;", "d",
                 "(Ljava/lang/String;Ljava/lang/String;Ljava/lang/Throwable;)I"},
                {"Landroid/util/Log;", "i",
                 "(Ljava/lang/String;Ljava/lang/String;)I"},
                {"Landroid/util/Log;", "i",
                 "(Ljava/lang/String;Ljava/lang/String;Ljava/lang/Throwable;)I"},
                {"Landroid/util/Log;", "w",
                 "(Ljava/lang/String;Ljava/lang/String;)I"},
                {"Landroid/util/Log;", "w",
                 "(Ljava/lang/String;Ljava/lang/String;Ljava/lang/Throwable;)I"},
                {"Landroid/util/Log;", "w",
                 "(Ljava/lang/String;Ljava/lang/Throwable;)I"},
                {"Landroid/util/Log;", "e",
                 "(Ljava/lang/String;Ljava/lang/String;)I"},
                {"Landroid/util/Log;", "e",
                 "(Ljava/lang/String;Ljava/lang/String;Ljava/lang/Throwable;)I"},
                {"Landroid/util/Log;", "wtf",
                 "(Ljava/lang/String;Ljava/lang/String;)I"},
                {"Landroid/util/Log;", "wtf",
                 "(Ljava/lang/String;Ljava/lang/String;Ljava/lang/Throwable;)I"},
                {"Landroid/util/Log;", "wtf",
                 "(Ljava/lang/String;Ljava/lang/Throwable;)I"},
                // Java standard output
                {"Ljava/io/PrintStream;", "println", "(Ljava/lang/String;)V"},
                {"Ljava/io/PrintStream;", "print",   "(Ljava/lang/String;)V"},

                // -------------------------------------------------------
                // SQLite — SQL injection via raw queries
                // -------------------------------------------------------
                {"Landroid/database/sqlite/SQLiteDatabase;", "execSQL",
                 "(Ljava/lang/String;)V"},
                {"Landroid/database/sqlite/SQLiteDatabase;", "execSQL",
                 "(Ljava/lang/String;[Ljava/lang/Object;)V"},
                {"Landroid/database/sqlite/SQLiteDatabase;", "rawQuery",
                 "(Ljava/lang/String;[Ljava/lang/String;)"
                 "Landroid/database/Cursor;"},

                // -------------------------------------------------------
                // Android WebView — tainted URL or JS
                // -------------------------------------------------------
                {"Landroid/webkit/WebView;", "loadUrl",
                 "(Ljava/lang/String;)V"},
                {"Landroid/webkit/WebView;", "loadData",
                 "(Ljava/lang/String;Ljava/lang/String;"
                 "Ljava/lang/String;)V"},
                {"Landroid/webkit/WebView;", "evaluateJavascript",
                 "(Ljava/lang/String;Landroid/webkit/ValueCallback;)V"},
                // Bridges a Java object into WebView's JS context — if the
                // bridged object carries tainted data (e.g. device
                // identifiers set as fields), JS content can read it back
                // out.  arg1 is the bridged Object, arg2 the JS-visible name.
                {"Landroid/webkit/WebView;", "addJavascriptInterface",
                 "(Ljava/lang/Object;Ljava/lang/String;)V"},

                // -------------------------------------------------------
                // SMS
                // -------------------------------------------------------
                {"Landroid/telephony/SmsManager;", "sendTextMessage",
                 "(Ljava/lang/String;Ljava/lang/String;Ljava/lang/String;"
                 "Landroid/app/PendingIntent;Landroid/app/PendingIntent;)V"},
                {"Landroid/telephony/SmsManager;", "sendDataMessage",
                 "(Ljava/lang/String;Ljava/lang/String;S[B"
                 "Landroid/app/PendingIntent;Landroid/app/PendingIntent;)V"},
                {"Landroid/telephony/SmsManager;", "sendMultipartTextMessage",
                 "(Ljava/lang/String;Ljava/lang/String;"
                 "Ljava/util/ArrayList;Ljava/util/ArrayList;"
                 "Ljava/util/ArrayList;)V"},

                // -------------------------------------------------------
                // Third-party cloud storage SDKs — file/object upload
                // -------------------------------------------------------
                {"Lcom/baidu/inf/iis/bcs/BaiduBCS;", "putObject",
                 "(Lcom/baidu/inf/iis/bcs/request/PutObjectRequest;)"
                 "Lcom/baidu/inf/iis/bcs/response/BaiduBCSResponse;"},

                // -------------------------------------------------------
                // JNDI
                // -------------------------------------------------------
                {"Ljavax/naming/InitialContext;", "lookup",
                 "(Ljava/lang/String;)Ljava/lang/Object;"},
                {"Ljavax/naming/directory/InitialDirContext;", "search",
                 "(Ljava/lang/String;Ljava/lang/String;"
                 "Ljavax/naming/directory/SearchControls;)"
                 "Ljavax/naming/NamingEnumeration;"},

                // -------------------------------------------------------
                // Reflection — dynamic dispatch / mutation with tainted data
                // -------------------------------------------------------
                // Class loading by tainted name
                {"Ljava/lang/Class;", "forName",
                 "(Ljava/lang/String;)Ljava/lang/Class;"},
                {"Ljava/lang/Class;", "forName",
                 "(Ljava/lang/String;ZLjava/lang/ClassLoader;)Ljava/lang/Class;"},
                {"Ljava/lang/ClassLoader;", "loadClass",
                 "(Ljava/lang/String;)Ljava/lang/Class;"},
                // Method field lookup by tainted name
                {"Ljava/lang/Class;", "getMethod",
                 "(Ljava/lang/String;[Ljava/lang/Class;)"
                 "Ljava/lang/reflect/Method;"},
                {"Ljava/lang/Class;", "getDeclaredMethod",
                 "(Ljava/lang/String;[Ljava/lang/Class;)"
                 "Ljava/lang/reflect/Method;"},
                {"Ljava/lang/Class;", "getField",
                 "(Ljava/lang/String;)Ljava/lang/reflect/Field;"},
                {"Ljava/lang/Class;", "getDeclaredField",
                 "(Ljava/lang/String;)Ljava/lang/reflect/Field;"},
                // Dynamic method invocation — callee is unknown statically;
                // treat invoke itself as a terminal sink so that any tainted
                // value in the Object[] args array is reported.
                {"Ljava/lang/reflect/Method;", "invoke",
                 "(Ljava/lang/Object;[Ljava/lang/Object;)"
                 "Ljava/lang/Object;"},
                // Dynamic constructor — tainted args reach new instance.
                {"Ljava/lang/reflect/Constructor;", "newInstance",
                 "([Ljava/lang/Object;)Ljava/lang/Object;"},
                // Reflective field write — tainted value stored via reflection.
                {"Ljava/lang/reflect/Field;", "set",
                 "(Ljava/lang/Object;Ljava/lang/Object;)V"},
                {"Ljava/lang/reflect/Field;", "setBoolean",
                 "(Ljava/lang/Object;Z)V"},
                {"Ljava/lang/reflect/Field;", "setByte",
                 "(Ljava/lang/Object;B)V"},
                {"Ljava/lang/reflect/Field;", "setChar",
                 "(Ljava/lang/Object;C)V"},
                {"Ljava/lang/reflect/Field;", "setDouble",
                 "(Ljava/lang/Object;D)V"},
                {"Ljava/lang/reflect/Field;", "setFloat",
                 "(Ljava/lang/Object;F)V"},
                {"Ljava/lang/reflect/Field;", "setInt",
                 "(Ljava/lang/Object;I)V"},
                {"Ljava/lang/reflect/Field;", "setLong",
                 "(Ljava/lang/Object;J)V"},
                {"Ljava/lang/reflect/Field;", "setShort",
                 "(Ljava/lang/Object;S)V"},

                // -------------------------------------------------------
                // Android OS IPC — Handler / Binder
                // -------------------------------------------------------
                {"Landroid/os/Handler;", "sendMessage",
                 "(Landroid/os/Message;)Z"},

                // -------------------------------------------------------
                // Android Bundle — packs tainted data into IPC bundles
                // -------------------------------------------------------
                {"Landroid/os/Bundle;", "putBinder",
                 "(Ljava/lang/String;Landroid/os/IBinder;)V"},
                {"Landroid/os/Bundle;", "putBoolean",
                 "(Ljava/lang/String;Z)V"},
                {"Landroid/os/Bundle;", "putBooleanArray",
                 "(Ljava/lang/String;[Z)V"},
                {"Landroid/os/Bundle;", "putBundle",
                 "(Ljava/lang/String;Landroid/os/Bundle;)V"},
                {"Landroid/os/Bundle;", "putByte",
                 "(Ljava/lang/String;B)V"},
                {"Landroid/os/Bundle;", "putByteArray",
                 "(Ljava/lang/String;[B)V"},
                {"Landroid/os/Bundle;", "putChar",
                 "(Ljava/lang/String;C)V"},
                {"Landroid/os/Bundle;", "putCharArray",
                 "(Ljava/lang/String;[C)V"},
                {"Landroid/os/Bundle;", "putCharSequence",
                 "(Ljava/lang/String;Ljava/lang/CharSequence;)V"},
                {"Landroid/os/Bundle;", "putCharSequenceArray",
                 "(Ljava/lang/String;[Ljava/lang/CharSequence;)V"},
                {"Landroid/os/Bundle;", "putCharSequenceArrayList",
                 "(Ljava/lang/String;Ljava/util/ArrayList;)V"},
                {"Landroid/os/Bundle;", "putDouble",
                 "(Ljava/lang/String;D)V"},
                {"Landroid/os/Bundle;", "putDoubleArray",
                 "(Ljava/lang/String;[D)V"},
                {"Landroid/os/Bundle;", "putFloat",
                 "(Ljava/lang/String;F)V"},
                {"Landroid/os/Bundle;", "putFloatArray",
                 "(Ljava/lang/String;[F)V"},
                {"Landroid/os/Bundle;", "putInt",
                 "(Ljava/lang/String;I)V"},
                {"Landroid/os/Bundle;", "putIntArray",
                 "(Ljava/lang/String;[I)V"},
                {"Landroid/os/Bundle;", "putIntegerArrayList",
                 "(Ljava/lang/String;Ljava/util/ArrayList;)V"},
                {"Landroid/os/Bundle;", "putLong",
                 "(Ljava/lang/String;J)V"},
                {"Landroid/os/Bundle;", "putLongArray",
                 "(Ljava/lang/String;[J)V"},
                {"Landroid/os/Bundle;", "putParcelable",
                 "(Ljava/lang/String;Landroid/os/Parcelable;)V"},
                {"Landroid/os/Bundle;", "putParcelableArray",
                 "(Ljava/lang/String;[Landroid/os/Parcelable;)V"},
                {"Landroid/os/Bundle;", "putParcelableArrayList",
                 "(Ljava/lang/String;Ljava/util/ArrayList;)V"},
                {"Landroid/os/Bundle;", "putSerializable",
                 "(Ljava/lang/String;Ljava/io/Serializable;)V"},
                {"Landroid/os/Bundle;", "putShort",
                 "(Ljava/lang/String;S)V"},
                {"Landroid/os/Bundle;", "putShortArray",
                 "(Ljava/lang/String;[S)V"},
                {"Landroid/os/Bundle;", "putSparseParcelableArray",
                 "(Ljava/lang/String;Landroid/util/SparseArray;)V"},
                {"Landroid/os/Bundle;", "putString",
                 "(Ljava/lang/String;Ljava/lang/String;)V"},
                {"Landroid/os/Bundle;", "putStringArray",
                 "(Ljava/lang/String;[Ljava/lang/String;)V"},
                {"Landroid/os/Bundle;", "putStringArrayList",
                 "(Ljava/lang/String;Ljava/util/ArrayList;)V"},
                {"Landroid/os/Bundle;", "putAll",
                 "(Landroid/os/Bundle;)V"},

                // -------------------------------------------------------
                // SharedPreferences.Editor — persisted storage leaks
                // -------------------------------------------------------
                {"Landroid/content/SharedPreferences$Editor;", "putBoolean",
                 "(Ljava/lang/String;Z)"
                 "Landroid/content/SharedPreferences$Editor;"},
                {"Landroid/content/SharedPreferences$Editor;", "putFloat",
                 "(Ljava/lang/String;F)"
                 "Landroid/content/SharedPreferences$Editor;"},
                {"Landroid/content/SharedPreferences$Editor;", "putInt",
                 "(Ljava/lang/String;I)"
                 "Landroid/content/SharedPreferences$Editor;"},
                {"Landroid/content/SharedPreferences$Editor;", "putLong",
                 "(Ljava/lang/String;J)"
                 "Landroid/content/SharedPreferences$Editor;"},
                {"Landroid/content/SharedPreferences$Editor;", "putString",
                 "(Ljava/lang/String;Ljava/lang/String;)"
                 "Landroid/content/SharedPreferences$Editor;"},
                // commit() itself carries no data argument, but the put*
                // calls above return `this`, so a tainted put chained into
                // .commit() contaminates the Editor receiver (same receiver
                // -contamination path noted for flush() above) — listing it
                // lets that chain be detected at its natural sink location.
                {"Landroid/content/SharedPreferences$Editor;", "commit",
                 "()Z"},

                // -------------------------------------------------------
                // ContentValues — tainted data staged for a DB insert/update
                // -------------------------------------------------------
                {"Landroid/content/ContentValues;", "put",
                 "(Ljava/lang/String;Ljava/lang/String;)V"},
                {"Landroid/content/ContentValues;", "put",
                 "(Ljava/lang/String;Ljava/lang/Integer;)V"},
                {"Landroid/content/ContentValues;", "put",
                 "(Ljava/lang/String;Ljava/lang/Long;)V"},

                // -------------------------------------------------------
                // MediaRecorder — tainted audio/video recording
                // -------------------------------------------------------
                {"Landroid/media/MediaRecorder;", "setVideoSource", "(I)V"},
                {"Landroid/media/MediaRecorder;", "setPreviewDisplay",
                 "(Landroid/view/Surface;)V"},
                {"Landroid/media/MediaRecorder;", "start", "()V"},

                // -------------------------------------------------------
                // Inter-App Communication — Intent construction & dispatch
                // -------------------------------------------------------
                // Intent mutation: setAction / setClassName / setComponent
                {"Landroid/content/Intent;", "setAction",
                 "(Ljava/lang/String;)Landroid/content/Intent;"},
                {"Landroid/content/Intent;", "setClassName",
                 "(Landroid/content/Context;Ljava/lang/Class;)"
                 "Landroid/content/Intent;"},
                {"Landroid/content/Intent;", "setClassName",
                 "(Landroid/content/Context;Ljava/lang/String;)"
                 "Landroid/content/Intent;"},
                {"Landroid/content/Intent;", "setComponent",
                 "(Landroid/content/ComponentName;)"
                 "Landroid/content/Intent;"},
                // Intent.putExtra overloads
                {"Landroid/content/Intent;", "putExtra",
                 "(Ljava/lang/String;Ljava/lang/String;)"
                 "Landroid/content/Intent;"},
                {"Landroid/content/Intent;", "putExtra",
                 "(Ljava/lang/String;I)Landroid/content/Intent;"},
                {"Landroid/content/Intent;", "putExtra",
                 "(Ljava/lang/String;Z)Landroid/content/Intent;"},
                {"Landroid/content/Intent;", "putExtra",
                 "(Ljava/lang/String;J)Landroid/content/Intent;"},
                {"Landroid/content/Intent;", "putExtra",
                 "(Ljava/lang/String;F)Landroid/content/Intent;"},
                {"Landroid/content/Intent;", "putExtra",
                 "(Ljava/lang/String;D)Landroid/content/Intent;"},
                {"Landroid/content/Intent;", "putExtra",
                 "(Ljava/lang/String;[Ljava/lang/String;)"
                 "Landroid/content/Intent;"},
                {"Landroid/content/Intent;", "putExtra",
                 "(Ljava/lang/String;Ljava/io/Serializable;)"
                 "Landroid/content/Intent;"},
                {"Landroid/content/Intent;", "putExtra",
                 "(Ljava/lang/String;Landroid/os/Parcelable;)"
                 "Landroid/content/Intent;"},
                {"Landroid/content/Intent;", "putExtra",
                 "(Ljava/lang/String;Landroid/os/Bundle;)"
                 "Landroid/content/Intent;"},
                {"Landroid/content/Intent;", "putExtras",
                 "(Landroid/os/Bundle;)Landroid/content/Intent;"},

                // Context.startActivity / startActivities
                {"Landroid/content/Context;", "startActivity",
                 "(Landroid/content/Intent;)V"},
                {"Landroid/content/Context;", "startActivity",
                 "(Landroid/content/Intent;Landroid/os/Bundle;)V"},
                {"Landroid/content/Context;", "startActivities",
                 "([Landroid/content/Intent;)V"},
                {"Landroid/content/Context;", "startActivities",
                 "([Landroid/content/Intent;Landroid/os/Bundle;)V"},

                // Activity dispatch methods
                {"Landroid/app/Activity;", "startActivityForResult",
                 "(Landroid/content/Intent;I)V"},
                {"Landroid/app/Activity;", "startActivityForResult",
                 "(Landroid/content/Intent;ILandroid/os/Bundle;)V"},
                {"Landroid/app/Activity;", "startActivities",
                 "([Landroid/content/Intent;)V"},
                {"Landroid/app/Activity;", "startActivities",
                 "([Landroid/content/Intent;Landroid/os/Bundle;)V"},
                {"Landroid/app/Activity;", "startActivityFromChild",
                 "(Landroid/app/Activity;Landroid/content/Intent;I)V"},
                {"Landroid/app/Activity;", "startActivityFromChild",
                 "(Landroid/app/Activity;Landroid/content/Intent;"
                 "ILandroid/os/Bundle;)V"},
                {"Landroid/app/Activity;", "startActivityFromFragment",
                 "(Landroid/app/Fragment;Landroid/content/Intent;I)V"},
                {"Landroid/app/Activity;", "startActivityFromFragment",
                 "(Landroid/app/Fragment;Landroid/content/Intent;"
                 "ILandroid/os/Bundle;)V"},
                {"Landroid/app/Activity;", "startActivityIfNeeded",
                 "(Landroid/content/Intent;I)Z"},
                {"Landroid/app/Activity;", "startActivityIfNeeded",
                 "(Landroid/content/Intent;ILandroid/os/Bundle;)Z"},
                {"Landroid/app/Activity;", "setResult",
                 "(ILandroid/content/Intent;)V"},

                // Service dispatch
                {"Landroid/content/Context;", "startService",
                 "(Landroid/content/Intent;)Landroid/content/ComponentName;"},
                {"Landroid/content/Context;", "startForegroundService",
                 "(Landroid/content/Intent;)Landroid/content/ComponentName;"},
                {"Landroid/content/Context;", "bindService",
                 "(Landroid/content/Intent;"
                 "Landroid/content/ServiceConnection;I)Z"},
                {"Landroid/app/Activity;", "startService",
                 "(Landroid/content/Intent;)Landroid/content/ComponentName;"},
                {"Landroid/app/Activity;", "bindService",
                 "(Landroid/content/Intent;"
                 "Landroid/content/ServiceConnection;I)Z"},

                // Broadcast dispatch — Context
                {"Landroid/content/Context;", "sendBroadcast",
                 "(Landroid/content/Intent;)V"},
                {"Landroid/content/Context;", "sendBroadcast",
                 "(Landroid/content/Intent;Ljava/lang/String;)V"},
                {"Landroid/content/Context;", "sendOrderedBroadcast",
                 "(Landroid/content/Intent;Ljava/lang/String;)V"},
                {"Landroid/content/Context;", "sendOrderedBroadcast",
                 "(Landroid/content/Intent;Ljava/lang/String;"
                 "Landroid/content/BroadcastReceiver;Landroid/os/Handler;"
                 "ILjava/lang/String;Landroid/os/Bundle;)V"},
                {"Landroid/content/Context;", "sendStickyBroadcast",
                 "(Landroid/content/Intent;)V"},
                // Broadcast dispatch — Activity (inherits Context but
                // FlowDroid lists Activity separately)
                {"Landroid/app/Activity;", "sendBroadcast",
                 "(Landroid/content/Intent;)V"},
                {"Landroid/app/Activity;", "sendBroadcast",
                 "(Landroid/content/Intent;Ljava/lang/String;)V"},
                {"Landroid/app/Activity;", "sendBroadcastAsUser",
                 "(Landroid/content/Intent;Landroid/os/UserHandle;)V"},
                {"Landroid/app/Activity;", "sendBroadcastAsUser",
                 "(Landroid/content/Intent;Landroid/os/UserHandle;"
                 "Ljava/lang/String;)V"},
                {"Landroid/app/Activity;", "sendOrderedBroadcast",
                 "(Landroid/content/Intent;Ljava/lang/String;)V"},
                {"Landroid/app/Activity;", "sendOrderedBroadcast",
                 "(Landroid/content/Intent;Ljava/lang/String;"
                 "Landroid/content/BroadcastReceiver;Landroid/os/Handler;"
                 "ILjava/lang/String;Landroid/os/Bundle;)V"},
                {"Landroid/app/Activity;", "sendOrderedBroadcastAsUser",
                 "(Landroid/content/Intent;Landroid/os/UserHandle;"
                 "Ljava/lang/String;Landroid/content/BroadcastReceiver;"
                 "Landroid/os/Handler;ILjava/lang/String;"
                 "Landroid/os/Bundle;)V"},
                {"Landroid/app/Activity;", "sendStickyBroadcast",
                 "(Landroid/content/Intent;)V"},
                {"Landroid/app/Activity;", "sendStickyBroadcastAsUser",
                 "(Landroid/content/Intent;Landroid/os/UserHandle;)V"},
                {"Landroid/app/Activity;", "sendStickyOrderedBroadcast",
                 "(Landroid/content/Intent;"
                 "Landroid/content/BroadcastReceiver;Landroid/os/Handler;"
                 "ILjava/lang/String;Landroid/os/Bundle;)V"},
                {"Landroid/app/Activity;", "sendStickyOrderedBroadcastAsUser",
                 "(Landroid/content/Intent;Landroid/os/UserHandle;"
                 "Landroid/content/BroadcastReceiver;Landroid/os/Handler;"
                 "ILjava/lang/String;Landroid/os/Bundle;)V"},
                // ContextWrapper
                {"Landroid/content/ContextWrapper;", "sendOrderedBroadcast",
                 "(Landroid/content/Intent;Ljava/lang/String;)V"},

                // Dynamic receiver registration — tainted IntentFilter action
                {"Landroid/content/Context;", "registerReceiver",
                 "(Landroid/content/BroadcastReceiver;"
                 "Landroid/content/IntentFilter;)"
                 "Landroid/content/Intent;"},
                {"Landroid/content/Context;", "registerReceiver",
                 "(Landroid/content/BroadcastReceiver;"
                 "Landroid/content/IntentFilter;"
                 "Ljava/lang/String;Landroid/os/Handler;)"
                 "Landroid/content/Intent;"},
                {"Landroid/content/IntentFilter;", "addAction",
                 "(Ljava/lang/String;)V"},

                // ContentResolver CRUD + cancellable query
                {"Landroid/content/ContentResolver;", "query",
                 "(Landroid/net/Uri;[Ljava/lang/String;Ljava/lang/String;"
                 "[Ljava/lang/String;Ljava/lang/String;)"
                 "Landroid/database/Cursor;"},
                {"Landroid/content/ContentResolver;", "query",
                 "(Landroid/net/Uri;[Ljava/lang/String;Ljava/lang/String;"
                 "[Ljava/lang/String;Ljava/lang/String;"
                 "Landroid/os/CancellationSignal;)"
                 "Landroid/database/Cursor;"},
                {"Landroid/content/ContentResolver;", "insert",
                 "(Landroid/net/Uri;Landroid/content/ContentValues;)"
                 "Landroid/net/Uri;"},
                {"Landroid/content/ContentResolver;", "update",
                 "(Landroid/net/Uri;Landroid/content/ContentValues;"
                 "Ljava/lang/String;[Ljava/lang/String;)I"},
                {"Landroid/content/ContentResolver;", "delete",
                 "(Landroid/net/Uri;Ljava/lang/String;"
                 "[Ljava/lang/String;)I"},
        };
    }

    // -----------------------------------------------------------------------
    // Default source specs — methods whose return values carry sensitive data.
    // Mirrors the Android subset of FlowDroid's SourcesAndSinks.txt.
    // -----------------------------------------------------------------------
    std::vector<SourceSpec> default_sources()
    {
        return {
                // Location
                {"Landroid/location/Location;", "getLatitude", "()D"},
                {"Landroid/location/Location;", "getLongitude", "()D"},
                {"Landroid/location/LocationManager;", "getLastKnownLocation",
                 "(Ljava/lang/String;)Landroid/location/Location;"},

                // Telephony / SIM identifiers
                {"Landroid/telephony/TelephonyManager;", "getDeviceId",
                 "()Ljava/lang/String;"},
                {"Landroid/telephony/TelephonyManager;", "getSubscriberId",
                 "()Ljava/lang/String;"},
                {"Landroid/telephony/TelephonyManager;", "getSimSerialNumber",
                 "()Ljava/lang/String;"},
                {"Landroid/telephony/TelephonyManager;", "getLine1Number",
                 "()Ljava/lang/String;"},
                {"Landroid/telephony/TelephonyManager;", "getSimCountryIso",
                 "()Ljava/lang/String;"},
                {"Landroid/telephony/TelephonyManager;", "getNetworkCountryIso",
                 "()Ljava/lang/String;"},
                {"Landroid/telephony/TelephonyManager;", "getNetworkOperator",
                 "()Ljava/lang/String;"},
                {"Landroid/telephony/TelephonyManager;", "getNetworkOperatorName",
                 "()Ljava/lang/String;"},

                // Cell location
                {"Landroid/telephony/gsm/GsmCellLocation;", "getCid", "()I"},
                {"Landroid/telephony/gsm/GsmCellLocation;", "getLac", "()I"},

                // Wi-Fi / Bluetooth identifiers
                {"Landroid/net/wifi/WifiInfo;", "getMacAddress",
                 "()Ljava/lang/String;"},
                {"Landroid/net/wifi/WifiInfo;", "getSSID",
                 "()Ljava/lang/String;"},
                {"Landroid/bluetooth/BluetoothAdapter;", "getAddress",
                 "()Ljava/lang/String;"},
                // getConnectionInfo() itself, in addition to WifiInfo's own
                // accessors above — some samples pass the whole WifiInfo
                // object onward (e.g. via toString()) rather than calling
                // getMacAddress/getSSID directly.
                {"Landroid/net/wifi/WifiManager;", "getConnectionInfo",
                 "()Landroid/net/wifi/WifiInfo;"},

                // Incoming SMS — PDU parsing and content/sender accessors.
                // createFromPdu is the standard BroadcastReceiver pattern for
                // android.provider.Telephony.SMS_RECEIVED; both the modern
                // and legacy (android.telephony.gsm) SmsMessage classes
                // appear across real-world samples.
                {"Landroid/telephony/SmsMessage;", "createFromPdu",
                 "([B)Landroid/telephony/SmsMessage;"},
                {"Landroid/telephony/gsm/SmsMessage;", "createFromPdu",
                 "([B)Landroid/telephony/gsm/SmsMessage;"},
                {"Landroid/telephony/SmsMessage;", "getDisplayMessageBody",
                 "()Ljava/lang/String;"},
                {"Landroid/telephony/gsm/SmsMessage;", "getDisplayMessageBody",
                 "()Ljava/lang/String;"},
                {"Landroid/telephony/SmsMessage;", "getMessageBody",
                 "()Ljava/lang/String;"},
                {"Landroid/telephony/gsm/SmsMessage;", "getMessageBody",
                 "()Ljava/lang/String;"},
                {"Landroid/telephony/SmsMessage;",
                 "getDisplayOriginatingAddress", "()Ljava/lang/String;"},
                {"Landroid/telephony/gsm/SmsMessage;",
                 "getDisplayOriginatingAddress", "()Ljava/lang/String;"},
                {"Landroid/telephony/SmsMessage;", "getOriginatingAddress",
                 "()Ljava/lang/String;"},
                {"Landroid/telephony/gsm/SmsMessage;", "getOriginatingAddress",
                 "()Ljava/lang/String;"},

                // Directory listing — enumerating device files (photos,
                // documents, etc.) as a precursor to exfiltrating them.
                {"Ljava/io/File;", "listFiles",
                 "()[Ljava/io/File;"},

                // UI widget content — reading user-typed input directly
                // (e.g. a fake login screen harvesting typed credentials),
                // as opposed to a value arriving via Intent/source API.
                {"Landroid/widget/EditText;", "getText",
                 "()Landroid/text/Editable;"},
                {"Landroid/widget/TextView;", "getText",
                 "()Ljava/lang/CharSequence;"},

                // Audio capture
                {"Landroid/media/AudioRecord;", "read", "([SII)I"},
                {"Landroid/media/AudioRecord;", "read", "([BII)I"},
                {"Landroid/media/AudioRecord;", "read",
                 "(Ljava/nio/ByteBuffer;I)I"},

                // Installed package enumeration
                {"Landroid/content/pm/PackageManager;",
                 "getInstalledApplications",
                 "(I)Ljava/util/List;"},
                {"Landroid/content/pm/PackageManager;",
                 "getInstalledPackages",
                 "(I)Ljava/util/List;"},
                {"Landroid/content/pm/PackageManager;",
                 "queryIntentActivities",
                 "(Landroid/content/Intent;I)Ljava/util/List;"},
                {"Landroid/content/pm/PackageManager;",
                 "queryIntentServices",
                 "(Landroid/content/Intent;I)Ljava/util/List;"},
                {"Landroid/content/pm/PackageManager;",
                 "queryBroadcastReceivers",
                 "(Landroid/content/Intent;I)Ljava/util/List;"},
                {"Landroid/content/pm/PackageManager;",
                 "queryContentProviders",
                 "(Ljava/lang/String;II)Ljava/util/List;"},

                // Account credentials
                {"Landroid/accounts/AccountManager;", "getAccounts",
                 "()[Landroid/accounts/Account;"},

                // Browser history / bookmarks
                // FlowDroid lists no-arg; real API also has a ContentResolver
                // overload — include both.
                {"Landroid/provider/Browser;", "getAllBookmarks",
                 "()Landroid/database/Cursor;"},
                {"Landroid/provider/Browser;", "getAllBookmarks",
                 "(Landroid/content/ContentResolver;)"
                 "Landroid/database/Cursor;"},
                {"Landroid/provider/Browser;", "getAllVisitedUrls",
                 "()Landroid/database/Cursor;"},
                {"Landroid/provider/Browser;", "getAllVisitedUrls",
                 "(Landroid/content/ContentResolver;)"
                 "Landroid/database/Cursor;"},

                // ContentResolver / Cursor — DB reads
                {"Landroid/content/ContentResolver;", "query",
                 "(Landroid/net/Uri;[Ljava/lang/String;Ljava/lang/String;"
                 "[Ljava/lang/String;Ljava/lang/String;)"
                 "Landroid/database/Cursor;"},
                {"Landroid/content/ContentResolver;", "query",
                 "(Landroid/net/Uri;[Ljava/lang/String;Ljava/lang/String;"
                 "[Ljava/lang/String;Ljava/lang/String;"
                 "Landroid/os/CancellationSignal;)"
                 "Landroid/database/Cursor;"},
                {"Landroid/database/Cursor;", "getString",
                 "(I)Ljava/lang/String;"},

                // SharedPreferences — stored data reads
                {"Landroid/content/SharedPreferences;",
                 "getDefaultSharedPreferences",
                 "(Landroid/content/Context;)"
                 "Landroid/content/SharedPreferences;"},

                // Locale / Calendar — device locale and timezone
                {"Ljava/util/Locale;", "getCountry",
                 "()Ljava/lang/String;"},
                {"Ljava/util/Calendar;", "getTimeZone",
                 "()Ljava/util/TimeZone;"},

                // HTTP response body — data received from network
                {"Lorg/apache/http/HttpResponse;", "getEntity",
                 "()Lorg/apache/http/HttpEntity;"},

                // File path exposure
                {"Ljava/io/File;", "getAbsoluteFile",
                 "()Ljava/io/File;"},
                {"Ljava/io/File;", "getCanonicalFile",
                 "()Ljava/io/File;"},

                // Network input streams (_BOTH_ in FlowDroid)
                {"Ljava/net/URLConnection;", "getInputStream",
                 "()Ljava/io/InputStream;"},
                {"Ljava/net/URL;", "openStream",
                 "()Ljava/io/InputStream;"},
                {"Ljava/net/URL;", "getContent",
                 "()Ljava/lang/Object;"},
                {"Ljava/net/URL;", "getContent",
                 "([Ljava/lang/Class;)Ljava/lang/Object;"},

                // SQLiteDatabase.query as source (FlowDroid lists these)
                {"Landroid/database/sqlite/SQLiteDatabase;", "query",
                 "(Landroid/net/Uri;[Ljava/lang/String;Ljava/lang/String;"
                 "[Ljava/lang/String;Ljava/lang/String;)"
                 "Landroid/database/Cursor;"},
                {"Landroid/database/sqlite/SQLiteDatabase;", "query",
                 "(Landroid/net/Uri;[Ljava/lang/String;Ljava/lang/String;"
                 "[Ljava/lang/String;Ljava/lang/String;"
                 "Landroid/os/CancellationSignal;)"
                 "Landroid/database/Cursor;"},

                // Android IPC — received Intent as source (ICC / reflection flows).
                // Activity.getIntent() returns the Intent that launched the component;
                // its extras carry data sent by the caller across app boundaries.
                {"Landroid/app/Activity;", "getIntent",
                 "()Landroid/content/Intent;"},
                // Intent extra accessors — the primary way receivers read IPC data.
                {"Landroid/content/Intent;", "getStringExtra",
                 "(Ljava/lang/String;)Ljava/lang/String;"},
                {"Landroid/content/Intent;", "getIntExtra",
                 "(Ljava/lang/String;I)I"},
                {"Landroid/content/Intent;", "getLongExtra",
                 "(Ljava/lang/String;J)J"},
                {"Landroid/content/Intent;", "getBooleanExtra",
                 "(Ljava/lang/String;Z)Z"},
                {"Landroid/content/Intent;", "getFloatExtra",
                 "(Ljava/lang/String;F)F"},
                {"Landroid/content/Intent;", "getDoubleExtra",
                 "(Ljava/lang/String;D)D"},
                {"Landroid/content/Intent;", "getByteExtra",
                 "(Ljava/lang/String;B)B"},
                {"Landroid/content/Intent;", "getCharExtra",
                 "(Ljava/lang/String;C)C"},
                {"Landroid/content/Intent;", "getShortExtra",
                 "(Ljava/lang/String;S)S"},
                {"Landroid/content/Intent;", "getStringArrayExtra",
                 "(Ljava/lang/String;)[Ljava/lang/String;"},
                {"Landroid/content/Intent;", "getStringArrayListExtra",
                 "(Ljava/lang/String;)Ljava/util/ArrayList;"},
                {"Landroid/content/Intent;", "getSerializableExtra",
                 "(Ljava/lang/String;)Ljava/io/Serializable;"},
                {"Landroid/content/Intent;", "getParcelableExtra",
                 "(Ljava/lang/String;)Landroid/os/Parcelable;"},
                {"Landroid/content/Intent;", "getBundleExtra",
                 "(Ljava/lang/String;)Landroid/os/Bundle;"},
                {"Landroid/content/Intent;", "getExtras",
                 "()Landroid/os/Bundle;"},
                {"Landroid/content/Intent;", "getData",
                 "()Landroid/net/Uri;"},
                {"Landroid/content/Intent;", "getAction",
                 "()Ljava/lang/String;"},
                // Bundle accessors — used when extras are extracted as a Bundle.
                {"Landroid/os/Bundle;", "getString",
                 "(Ljava/lang/String;)Ljava/lang/String;"},
                {"Landroid/os/Bundle;", "getString",
                 "(Ljava/lang/String;Ljava/lang/String;)Ljava/lang/String;"},
                {"Landroid/os/Bundle;", "getInt",
                 "(Ljava/lang/String;)I"},
                {"Landroid/os/Bundle;", "getInt",
                 "(Ljava/lang/String;I)I"},
                {"Landroid/os/Bundle;", "getLong",
                 "(Ljava/lang/String;)J"},
                {"Landroid/os/Bundle;", "getLong",
                 "(Ljava/lang/String;J)J"},
                {"Landroid/os/Bundle;", "getBoolean",
                 "(Ljava/lang/String;)Z"},
                {"Landroid/os/Bundle;", "getSerializable",
                 "(Ljava/lang/String;)Ljava/io/Serializable;"},
                {"Landroid/os/Bundle;", "getParcelable",
                 "(Ljava/lang/String;)Landroid/os/Parcelable;"},
        };
    }
}

InterprocParamResult run_interproc_param_taint(virtual_machine& vm,
                                               const InterprocParamConfig& config)
{
    InterprocParamResult result;
    auto cg = build_call_graph(vm);
    auto sinks = config.sinks.empty() ? default_sinks() : config.sinks;
    auto sources = config.sources.empty() ? default_sources() : config.sources;

    auto is_source_method = [&](const MethodId& mid,
                                const method_vertex_descriptor& mv) {
        if (!config.source_methods.empty()) {
            return std::find(config.source_methods.begin(),
                             config.source_methods.end(),
                             mid)
                    != config.source_methods.end();
        }
        // Skip methods whose class descriptor starts with an excluded prefix.
        // This suppresses param-taint seeding for bundled library code
        // (e.g. android/support/*, androidx/*) without affecting source-to-sink
        // detection, which runs in an independent domain.
        if (!config.param_seed_exclude_prefixes.empty()) {
            const auto& desc = mid.type.descriptor;
            for (const auto& pfx : config.param_seed_exclude_prefixes) {
                if (desc.size() >= pfx.size()
                        && desc.compare(0, pfx.size(), pfx) == 0) {
                    return false;
                }
            }
        }
        if (config.seed_public_only) {
            return (vm.methods()[mv].access_flags & acc_public) != 0;
        }
        // Skip private methods with no callers: they are dead code unreachable
        // from any entry point, so seeding them only generates false positives.
        if (config.skip_private_no_callers) {
            bool is_private =
                    (vm.methods()[mv].access_flags & acc_private) != 0;
            if (is_private) {
                auto it = cg.callers.find(mid);
                if (it == cg.callers.end() || it->second.empty()) {
                    return false;
                }
            }
        }
        // Default: seed all methods.
        return true;
    };

    // Top-down, demand-driven context-sensitive analysis.
    //
    // For each seed method (whose parameters are taint sources), create a
    // CallContext with all parameters tainted and invoke get_or_compute_ctx.
    // That function will recursively analyse every callee it encounters,
    // passing only the taint that actually flows to each callee's parameters.
    CtxCache cache;

    for (const auto& entry : cg.method_vertices) {
        const auto& mid = entry.first;
        auto mv = entry.second;

        if (!is_source_method(mid, mv)) {
            continue;
        }

        const auto& ig = vm.methods()[mv].insns;
        const auto param_count = ig[boost::graph_bundle].ins_size;

        // Seed: all params of this method are tainted.
        CallContext entry_ctx(param_count);
        entry_ctx.set();
        // No caller passing source-tainted args at a true entry point — only
        // a direct source-API call inside the method itself can set src taint.
        CallContext entry_src_ctx(param_count);

        // Reset the work budget per seed method: a pathological
        // mutually-recursive cluster reachable from one seed shouldn't
        // starve the budget for every other, unrelated seed method.
        cache.compute_calls = 0;
        auto sum = get_or_compute_ctx(vm, mid, cg, entry_ctx, entry_src_ctx,
                                      cache,
                                      config.lib_policy, sinks,
                                      result.sink_hits,
                                      sources, result.source_sink_hits);

        // Store summary (union across any additional contexts later).
        auto& cur = result.summaries[mid];
        cur.param_count = sum.param_count;
        if (cur.return_dep.size() < sum.return_dep.size()) {
            cur.return_dep.resize(sum.return_dep.size());
        }
        cur.return_dep |= sum.return_dep;
    }

    // Collect summaries for callee methods that were analysed on demand.
    // For display, union all contexts for each method.
    for (const auto& kv : cache.summaries) {
        auto& cur = result.summaries[kv.first.mid];
        if (cur.param_count == 0) {
            cur.param_count = kv.second.param_count;
        }
        if (cur.return_dep.size() < kv.second.return_dep.size()) {
            cur.return_dep.resize(kv.second.return_dep.size());
        }
        cur.return_dep |= kv.second.return_dep;
    }

    // Lifecycle second pass: propagate source-taint across Android component
    // lifecycle method boundaries.  For each component class that is a subtype
    // of Activity/Service/BroadcastReceiver/ContentProvider/Application,
    // re-analyse its lifecycle methods in lifecycle order, accumulating
    // source_field_writes from each method and feeding them into the next one
    // as pre_src_field_taint.  This makes source-tainted data stored via iput
    // in one callback (e.g. onCreate) visible to iget reads in a later callback
    // (e.g. onResume) even though the two are not connected in the call graph.
    //
    // Phase 1 runs Application components first and collects their static field
    // writes (global_app_sfw).  Phase 2 runs all components pre-seeded with
    // global_app_sfw so that Application-written static data flows into Activity/
    // Service callbacks (e.g. ApplicationLifecycle tests).
    if (config.model_android_lifecycle && !sources.empty()) {
        const auto& class_graph = vm.classes();

        struct ComponentInfo {
            const ComponentLifecycleTable* ctbl{nullptr};
            std::vector<std::pair<int, MethodId>> ordered_methods;
        };

        // Returns ComponentInfo for cv; empty ctbl if not an app-level component.
        auto collect_component_info = [&](class_vertex_descriptor cv_arg)
            -> ComponentInfo
        {
            ComponentInfo info;
            const auto& class_desc = class_graph[cv_arg].jvm_hdl.descriptor;
            if (class_desc.empty()) return info;
            if (class_desc.rfind("Landroid/", 0) == 0
                || class_desc.rfind("Ljava/", 0) == 0
                || class_desc.rfind("Lkotlin/", 0) == 0
                || class_desc.rfind("Landroidx/", 0) == 0
                || class_desc.rfind("Lcom/google/", 0) == 0) {
                return info;
            }

            std::unordered_set<std::string> supertypes;
            collect_supertype_descriptors(cv_arg, class_graph, supertypes);

            for (std::size_t ti = 0; ti < kComponentLifecyclesLen; ++ti) {
                if (supertypes.count(kComponentLifecycles[ti].base_descriptor)) {
                    info.ctbl = &kComponentLifecycles[ti];
                    break;
                }
            }
            if (!info.ctbl) return info;

            // BFS supertype chain (most-derived first, stops at framework).
            std::vector<std::string> super_chain;
            {
                std::queue<class_vertex_descriptor> bfs;
                bfs.push(cv_arg);
                std::unordered_set<std::string> bfs_visited;
                while (!bfs.empty()) {
                    auto bcur = bfs.front();
                    bfs.pop();
                    const auto& bd = class_graph[bcur].jvm_hdl.descriptor;
                    if (!bfs_visited.insert(bd).second) continue;
                    if (bd.rfind("Landroid/", 0) != 0
                        && bd.rfind("Ljava/", 0) != 0
                        && bd.rfind("Lkotlin/", 0) != 0
                        && bd.rfind("Landroidx/", 0) != 0
                        && bd.rfind("Lcom/google/", 0) != 0) {
                        super_chain.push_back(bd);
                    }
                    for (const auto& be :
                         boost::make_iterator_range(in_edges(bcur, class_graph))) {
                        const auto* bprop = boost::type_erasure::any_cast<
                                const class_super_edge_property*>(
                                &class_graph[be]);
                        if (bprop) bfs.push(source(be, class_graph));
                    }
                }
            }

            // Collect lifecycle methods (most-derived override wins).
            for (std::size_t li = 0; li < info.ctbl->len; ++li) {
                const auto& entry = info.ctbl->entries[li];
                bool found = false;
                for (const auto& sc : super_chain) {
                    for (const auto& me : cg.method_vertices) {
                        const auto& mid2 = me.first;
                        if (mid2.type.descriptor == sc
                            && mid2.name == entry.name
                            && mid2.descriptor == entry.descriptor) {
                            info.ordered_methods.push_back({entry.order, mid2});
                            found = true;
                            break;
                        }
                    }
                    if (found) break;
                }
            }
            std::sort(info.ordered_methods.begin(), info.ordered_methods.end(),
                      [](const auto& a, const auto& b) {
                          return a.first < b.first;
                      });

            // For Activity subclasses: also run methods registered via
            // android:onClick XML attribute — these take (View)V and are
            // called directly by the framework, not via OnClickListener.
            if (std::string(info.ctbl->base_descriptor)
                    == "Landroid/app/Activity;") {
                static const std::string kViewSig{"(Landroid/view/View;)V"};
                std::unordered_set<std::string> already_named;
                for (const auto& om : info.ordered_methods)
                    already_named.insert(om.second.name);
                int view_order = 50;
                for (const auto& sc : super_chain) {
                    for (const auto& me : cg.method_vertices) {
                        const auto& mid2 = me.first;
                        if (mid2.type.descriptor == sc
                                && mid2.descriptor == kViewSig
                                && !already_named.count(mid2.name)) {
                            info.ordered_methods.push_back({view_order++, mid2});
                            already_named.insert(mid2.name);
                        }
                    }
                }
            }

            return info;
        };

        // Run lifecycle analysis for one component, pre-seeded with pre_sfw.
        // Returns the final accumulated source_field_writes.
        auto run_lifecycle = [&](
                class_vertex_descriptor /* cv */,
                const ComponentInfo& info,
                const std::unordered_set<std::string>& pre_sfw)
            -> std::unordered_set<std::string>
        {
            std::unordered_set<std::string> accumulated = pre_sfw;
            for (const auto& om : info.ordered_methods) {
                const auto& lmid = om.second;
                auto mv_it2 = cg.method_vertices.find(lmid);
                if (mv_it2 == cg.method_vertices.end()) continue;
                const auto& ig2 = vm.methods()[mv_it2->second].insns;
                if (num_vertices(ig2) == 0) continue;
                const auto param_count2 = ig2[boost::graph_bundle].ins_size;
                CallContext lctx(param_count2);
                lctx.set();
                // True entry point: no caller passing source-tainted args.
                CallContext lsrc_ctx(param_count2);
                // Reset the work budget per lifecycle callback (see
                // CtxCache::compute_calls).
                cache.compute_calls = 0;
                auto lsum = compute_summary_ctx(
                        vm, lmid, mv_it2->second, cg, lctx, lsrc_ctx,
                        accumulated,
                        cache, config.lib_policy, sinks,
                        result.sink_hits, sources,
                        result.source_sink_hits);
                for (const auto& k : lsum.source_field_writes) {
                    accumulated.insert(k);
                }
            }
            return accumulated;
        };

        // Phase 1: ContentProvider then Application — collect static field writes.
        // ContentProvider.onCreate() is invoked by Android before Application.onCreate()
        // so we run ContentProviders first and seed Application with their SFW.
        std::unordered_set<std::string> global_app_sfw;
        // Phase 1a: ContentProvider subclasses.
        for (auto [cv, cv_end] = vertices(class_graph); cv != cv_end; ++cv) {
            auto info = collect_component_info(*cv);
            if (!info.ctbl) continue;
            if (std::string(info.ctbl->base_descriptor)
                    != "Landroid/content/ContentProvider;") {
                continue;
            }
            if (info.ordered_methods.empty()) continue;
            auto acc = run_lifecycle(*cv, info, {});
            for (const auto& k : acc) {
                if (k.rfind("STATIC:", 0) == 0) global_app_sfw.insert(k);
            }
        }
        // Phase 1b: Application subclasses, seeded with ContentProvider SFW.
        for (auto [cv, cv_end] = vertices(class_graph); cv != cv_end; ++cv) {
            auto info = collect_component_info(*cv);
            if (!info.ctbl) continue;
            if (std::string(info.ctbl->base_descriptor)
                    != "Landroid/app/Application;") {
                continue;
            }
            if (info.ordered_methods.empty()) continue;
            auto acc = run_lifecycle(*cv, info, global_app_sfw);
            for (const auto& k : acc) {
                if (k.rfind("STATIC:", 0) == 0) global_app_sfw.insert(k);
            }
        }

        // Phase 2a: always_run=true callback interfaces (LocationListener,
        // OnClickListener, etc.).  For each such callback table, find ALL
        // user classes that implement it (regardless of what else they extend)
        // and run those callback methods.  This correctly handles:
        //  (a) inner classes implementing the interface (separate class from Activity)
        //  (b) Activity/Service implementing the interface directly
        // Collect their SFW into global_callback_sfw so that the component
        // lifecycle pass (Phase 2b) can be pre-seeded with the results.
        std::unordered_set<std::string> global_callback_sfw;
        for (std::size_t ti = 0; ti < kComponentLifecyclesLen; ++ti) {
            if (!kComponentLifecycles[ti].always_run) continue;
            const auto& ctbl = kComponentLifecycles[ti];
            for (auto [cv, cv_end] = vertices(class_graph);
                 cv != cv_end; ++cv) {
                const auto& class_desc =
                        class_graph[*cv].jvm_hdl.descriptor;
                if (class_desc.empty()) continue;
                // Skip framework classes.
                if (class_desc.rfind("Landroid/", 0) == 0
                    || class_desc.rfind("Ljava/", 0) == 0
                    || class_desc.rfind("Lkotlin/", 0) == 0
                    || class_desc.rfind("Landroidx/", 0) == 0
                    || class_desc.rfind("Lcom/google/", 0) == 0) {
                    continue;
                }
                std::unordered_set<std::string> supertypes;
                collect_supertype_descriptors(*cv, class_graph, supertypes);
                if (!supertypes.count(ctbl.base_descriptor)) continue;

                // Build super chain for method lookup.
                std::vector<std::string> super_chain;
                {
                    std::queue<class_vertex_descriptor> bfs2;
                    bfs2.push(*cv);
                    std::unordered_set<std::string> bfs2_visited;
                    while (!bfs2.empty()) {
                        auto bcur = bfs2.front(); bfs2.pop();
                        const auto& bd = class_graph[bcur].jvm_hdl.descriptor;
                        if (!bfs2_visited.insert(bd).second) continue;
                        if (bd.rfind("Landroid/", 0) != 0
                            && bd.rfind("Ljava/", 0) != 0
                            && bd.rfind("Lkotlin/", 0) != 0
                            && bd.rfind("Landroidx/", 0) != 0
                            && bd.rfind("Lcom/google/", 0) != 0) {
                            super_chain.push_back(bd);
                        }
                        for (const auto& be : boost::make_iterator_range(
                                 in_edges(bcur, class_graph))) {
                            const auto* bprop =
                                boost::type_erasure::any_cast<
                                    const class_super_edge_property*>(
                                    &class_graph[be]);
                            if (bprop) bfs2.push(source(be, class_graph));
                        }
                    }
                }

                ComponentInfo cb_info;
                cb_info.ctbl = &ctbl;
                for (std::size_t li = 0; li < ctbl.len; ++li) {
                    const auto& entry = ctbl.entries[li];
                    bool found = false;
                    for (const auto& sc : super_chain) {
                        for (const auto& me : cg.method_vertices) {
                            const auto& mid2 = me.first;
                            if (mid2.type.descriptor == sc
                                && mid2.name == entry.name
                                && mid2.descriptor == entry.descriptor) {
                                cb_info.ordered_methods.push_back(
                                        {entry.order, mid2});
                                found = true;
                                break;
                            }
                        }
                        if (found) break;
                    }
                }
                if (cb_info.ordered_methods.empty()) continue;
                std::sort(cb_info.ordered_methods.begin(),
                          cb_info.ordered_methods.end(),
                          [](const auto& a, const auto& b) {
                              return a.first < b.first;
                          });

                auto acc = run_lifecycle(*cv, cb_info, global_app_sfw);
                for (const auto& k : acc)
                    global_callback_sfw.insert(k);
            }
        }

        // Phase 2b: All remaining component classes (Activities, Services, etc.),
        // pre-seeded with Application's static SFW AND callback SFW.
        // The callback SFW typically contains "FIELD:" entries written by listener
        // callbacks into outer-class fields, making those reads source-tainted in
        // the component's own lifecycle methods.
        std::unordered_set<std::string> combined_seed = global_app_sfw;
        for (const auto& k : global_callback_sfw)
            combined_seed.insert(k);

        // Phase 2b: component lifecycle classes — collect accumulated SFW
        // into global_component_sfw for use in Phase 2c (Runnable/Thread).
        // Each component is run twice when the first pass produces instance-field
        // SFW (P{n}:{fkey} keys), modeling lifecycle re-entry (e.g. Activity
        // recreation: onSaveInstanceState writes a field that onRestoreInstanceState
        // reads on the next lifecycle run).
        std::unordered_set<std::string> global_component_sfw = combined_seed;
        for (auto [cv, cv_end] = vertices(class_graph); cv != cv_end; ++cv) {
            auto info = collect_component_info(*cv);
            if (!info.ctbl) continue;
            if (info.ctbl->always_run) continue;  // already ran in Phase 2a
            if (info.ordered_methods.empty()) continue;
            auto acc = run_lifecycle(*cv, info, combined_seed);
            // Second pass: if the first pass produced instance-field SFW keys
            // (P{n}:{fkey}), re-run to model cross-lifecycle-run flows.
            bool has_instance_sfw = false;
            for (const auto& k : acc) {
                if (!k.empty() && k[0] == 'P') { has_instance_sfw = true; break; }
            }
            if (has_instance_sfw) {
                acc = run_lifecycle(*cv, info, acc);
            }
            for (const auto& k : acc) global_component_sfw.insert(k);
        }

        // Phase 2b cross-component pass: if any component wrote a STATIC SFW
        // that wasn't in the initial combined_seed (e.g. Activity2 writing
        // Activity1.data1, or Activity writing MyView.deviceID), re-run all
        // components once more with the fully-accumulated global_component_sfw
        // so that cross-Activity/cross-View static field flows are detected.
        {
            bool has_new_static = false;
            for (const auto& k : global_component_sfw) {
                if (k.rfind("STATIC:", 0) == 0
                    && !combined_seed.count(k)) {
                    has_new_static = true;
                    break;
                }
            }
            if (has_new_static) {
                for (auto [cv2, cv2_end] = vertices(class_graph);
                     cv2 != cv2_end; ++cv2) {
                    auto info2 = collect_component_info(*cv2);
                    if (!info2.ctbl) continue;
                    if (info2.ctbl->always_run) continue;
                    if (info2.ordered_methods.empty()) continue;
                    auto acc2 = run_lifecycle(*cv2, info2, global_component_sfw);
                    for (const auto& k : acc2) global_component_sfw.insert(k);
                }
            }
        }

        // Phase 2c: Thread/Runnable run() methods.
        // Seeds each user-defined class that owns a concrete run()V with all
        // SFW accumulated from component lifecycles.  This propagates source-
        // tainted fields written during Activity.onCreate (e.g. via Thread
        // subclass constructors) into the corresponding run() body.
        if (!global_component_sfw.empty()) {
            for (auto [cv, cv_end] = vertices(class_graph);
                 cv != cv_end; ++cv) {
                const auto& class_desc
                        = class_graph[*cv].jvm_hdl.descriptor;
                if (class_desc.empty()) continue;
                // Skip framework classes.
                if (class_desc.rfind("Landroid/", 0) == 0
                    || class_desc.rfind("Ljava/", 0) == 0
                    || class_desc.rfind("Lkotlin/", 0) == 0
                    || class_desc.rfind("Landroidx/", 0) == 0
                    || class_desc.rfind("Lcom/google/", 0) == 0) {
                    continue;
                }
                // Skip classes already handled as components (Activity etc.).
                {
                    auto info = collect_component_info(*cv);
                    if (info.ctbl) continue;
                }
                // Find run()V declared directly in this class.
                MethodId run_mid;
                bool found_run = false;
                for (const auto& me : cg.method_vertices) {
                    const auto& mid2 = me.first;
                    if (mid2.type.descriptor == class_desc
                        && mid2.name == "run"
                        && mid2.descriptor == "()V") {
                        run_mid = mid2;
                        found_run = true;
                        break;
                    }
                }
                if (!found_run) continue;
                // Static dummy table (only ctbl != nullptr is checked).
                static const LifecycleEntry kRunEntry_[]
                        = {{"run", "()V", 0}};
                static const ComponentLifecycleTable kRunTable_{
                        "Ljava/lang/Runnable;", kRunEntry_, 1, true};
                ComponentInfo run_info;
                run_info.ctbl = &kRunTable_;
                run_info.ordered_methods.push_back({0, run_mid});
                run_lifecycle(*cv, run_info, global_component_sfw);
            }
        }

        // Phase 2d: static initializers (<clinit>) for user-defined classes.
        // Static initializers run implicitly on first class use; here we model
        // them by running each <clinit>()V seeded with global_component_sfw so
        // that source-tainted static fields written by lifecycle methods are
        // visible (StaticInitialization1: Activity writes im → <clinit> sinks it).
        // After collecting <clinit> SFW, re-run all component lifecycles once
        // so that source-derived static fields written by <clinit> are seen by
        // subsequent lifecycle methods (StaticInitialization2: <clinit> writes im,
        // then Activity.onCreate sinks it).
        {
            std::unordered_set<std::string> clinit_sfw;
            static const LifecycleEntry kClinitEntry_[] = {{"<clinit>", "()V", 0}};
            static const ComponentLifecycleTable kClinitTable_{
                    "", kClinitEntry_, 1, true};

            for (auto [cv, cv_end] = vertices(class_graph); cv != cv_end; ++cv) {
                const auto& class_desc = class_graph[*cv].jvm_hdl.descriptor;
                if (class_desc.empty()) continue;
                if (class_desc.rfind("Landroid/", 0) == 0
                    || class_desc.rfind("Ljava/", 0) == 0
                    || class_desc.rfind("Lkotlin/", 0) == 0
                    || class_desc.rfind("Landroidx/", 0) == 0
                    || class_desc.rfind("Lcom/google/", 0) == 0
                    || class_desc.rfind("Landroid/support/", 0) == 0) {
                    continue;
                }
                MethodId clinit_mid;
                bool found = false;
                for (const auto& me : cg.method_vertices) {
                    if (me.first.type.descriptor == class_desc
                        && me.first.name == "<clinit>"
                        && me.first.descriptor == "()V") {
                        clinit_mid = me.first;
                        found = true;
                        break;
                    }
                }
                if (!found) continue;
                ComponentInfo ci;
                ci.ctbl = &kClinitTable_;
                ci.ordered_methods.push_back({0, clinit_mid});
                auto acc = run_lifecycle(*cv, ci, global_component_sfw);
                for (const auto& k : acc) {
                    if (k.rfind("STATIC:", 0) == 0) clinit_sfw.insert(k);
                }
            }

            // If <clinit> methods produced new static SFW, do one more
            // lifecycle pass so component methods can sink that data.
            if (!clinit_sfw.empty()) {
                std::unordered_set<std::string> seed2 = global_component_sfw;
                for (const auto& k : clinit_sfw) seed2.insert(k);
                for (auto [cv, cv_end] = vertices(class_graph);
                     cv != cv_end; ++cv) {
                    auto info = collect_component_info(*cv);
                    if (!info.ctbl) continue;
                    if (info.ctbl->always_run) continue;
                    if (info.ordered_methods.empty()) continue;
                    run_lifecycle(*cv, info, seed2);
                }
            }
        }
    }

    // Deduplicate sink hits: keep only one entry per unique (caller, callee,
    // offset) triple.  The inner fixpoint loop can emit the same call site
    // multiple times across iterations; deduplication removes those copies.
    {
        using Key = std::tuple<MethodId, MethodId, uint32_t>;
        struct KeyHash {
            std::size_t operator()(const Key& k) const
            {
                auto h1 = MethodIdHash{}(std::get<0>(k));
                auto h2 = MethodIdHash{}(std::get<1>(k));
                auto h3 = std::hash<uint32_t>{}(std::get<2>(k));
                return h1 ^ (h2 << 1) ^ (h3 << 2);
            }
        };
        struct KeyEq {
            bool operator()(const Key& a, const Key& b) const
            {
                return std::get<0>(a) == std::get<0>(b)
                       && std::get<1>(a) == std::get<1>(b)
                       && std::get<2>(a) == std::get<2>(b);
            }
        };
        std::unordered_map<Key, std::size_t, KeyHash, KeyEq> seen;
        std::vector<SinkHit> deduped;
        for (auto& hit : result.sink_hits) {
            Key k{hit.caller, hit.callee, hit.offset};
            if (seen.find(k) == seen.end()) {
                seen[k] = deduped.size();
                deduped.push_back(std::move(hit));
            }
        }
        result.sink_hits = std::move(deduped);
    }

    // Deduplicate source-to-sink hits.
    {
        using Key = std::tuple<MethodId, MethodId, uint32_t>;
        struct KeyHash {
            std::size_t operator()(const Key& k) const
            {
                auto h1 = MethodIdHash{}(std::get<0>(k));
                auto h2 = MethodIdHash{}(std::get<1>(k));
                auto h3 = std::hash<uint32_t>{}(std::get<2>(k));
                return h1 ^ (h2 << 1) ^ (h3 << 2);
            }
        };
        struct KeyEq {
            bool operator()(const Key& a, const Key& b) const
            {
                return std::get<0>(a) == std::get<0>(b)
                       && std::get<1>(a) == std::get<1>(b)
                       && std::get<2>(a) == std::get<2>(b);
            }
        };
        std::unordered_map<Key, std::size_t, KeyHash, KeyEq> seen;
        std::vector<SourceHit> deduped;
        for (auto& hit : result.source_sink_hits) {
            Key k{hit.caller, hit.sink_callee, hit.sink_offset};
            if (seen.find(k) == seen.end()) {
                seen[k] = deduped.size();
                deduped.push_back(std::move(hit));
            }
        }
        result.source_sink_hits = std::move(deduped);
    }

    return result;
}

} // namespace dfa
} // namespace analysis
} // namespace jitana
