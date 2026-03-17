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
    static std::string get_field_key(virtual_machine& vm, const insn& insn_obj)
    {
        auto fhdl_ptr = const_val<dex_field_hdl>(insn_obj);
        if (!fhdl_ptr) {
            return "";
        }
        auto jfhdl = vm.make_jvm_hdl(*fhdl_ptr);
        return jfhdl.type_hdl.descriptor + "." + jfhdl.unique_name;
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

    MethodId make_method_id_local(const virtual_machine& vm,
                                  const dex_method_hdl& hdl)
    {
        return make_method_id_local(vm.make_jvm_hdl(hdl));
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
        bool operator==(const CtxKey& o) const
        {
            return mid == o.mid && ctx == o.ctx;
        }
    };

    struct CtxKeyHash {
        std::size_t operator()(const CtxKey& k) const
        {
            std::size_t h = MethodIdHash{}(k.mid);
            boost::hash_combine(h, hash_call_context(k.ctx));
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
    };

    // Forward declaration — compute_summary_ctx and get_or_compute_ctx are
    // mutually recursive.
    static MethodSummary get_or_compute_ctx(
            virtual_machine& vm,
            const MethodId& mid,
            const CallGraph& cg,
            const CallContext& ctx,
            CtxCache& cache,
            LibPolicy lib_policy,
            const std::vector<SinkSpec>& sinks,
            std::vector<SinkHit>& sink_hits);

    // Intra-method dataflow analysis for one (method, entry context) pair.
    // entry_ctx specifies which of the method's own params are tainted at entry.
    // Calls back into get_or_compute_ctx for each callee encountered.
    static MethodSummary compute_summary_ctx(
            virtual_machine& vm,
            const MethodId& mid,
            const method_vertex_descriptor& mv,
            const CallGraph& cg,
            const CallContext& entry_ctx,
            CtxCache& cache,
            LibPolicy lib_policy,
            const std::vector<SinkSpec>& sinks,
            std::vector<SinkHit>& sink_hits)
    {
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

        // Flow-insensitive field taint: tracks which source params taint each
        // field within this method.  Grows monotonically; convergence is
        // guaranteed.  Keyed by stable JVM field descriptor.
        FieldTaintMap field_taint;

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
                    if (auto cv = lookup_class_vertex(m.type, vm.classes())) {
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

        bool changed = true;
        while (changed) {
            changed = false;
            for (std::size_t i = 0; i < n; ++i) {
                const auto v = order[i];
                auto new_in = make_zero_frame();
                DepSet incoming = DepSet(sum.param_count);
                bool saw_pred = false;
                for (auto ee = in_edges(v, ig); ee.first != ee.second; ++ee.first) {
                    auto pred = source(*ee.first, ig);
                    if (pred < index_of.size()) {
                        auto pred_idx = index_of[pred];
                        if (pred_idx < n) {
                            for (std::size_t r = 0; r < reg_domain; ++r) {
                                new_in[r] |= OUT[pred_idx][r];
                            }
                            incoming |= pending[pred_idx];
                            saw_pred = true;
                        }
                    }
                }
                if (!saw_pred) {
                    new_in = param_seed;
                }

                auto new_out = new_in;
                for (auto reg : DEF[i]) {
                    if (reg < new_out.size()) {
                        new_out[reg].reset();
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
                        auto maybe_report_sink = [&](const MethodId& callee_mid) {
                            if (!is_sink(callee_mid)) return;
                            std::vector<std::size_t> tainted_args;
                            for (std::size_t ai = 0; ai < invoke->args.size();
                                 ++ai) {
                                auto arg_reg = invoke->args[ai];
                                if (arg_reg < new_in.size()
                                    && new_in[arg_reg].any()) {
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

                        CallSiteId cs{mid, ig[v].off};
                        auto targets_it = cg.callees.find(cs);
                        if (targets_it != cg.callees.end()) {
                            for (const auto& tgt : targets_it->second) {
                                maybe_report_sink(tgt);
                            }
                        } else {
                            maybe_report_sink(invoke->callee);
                        }

                        // Derive the callee's context: which of its params
                        // are tainted based on the actual argument registers.
                        CallContext callee_ctx(invoke->args.size());
                        for (std::size_t pi = 0; pi < invoke->args.size();
                             ++pi) {
                            auto arg_reg = invoke->args[pi];
                            if (arg_reg < new_in.size()
                                && new_in[arg_reg].any()) {
                                callee_ctx.set(pi);
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
                            MethodSummary callee_sum;
                            if (callee_ctx.none()) {
                                // No tainted args — return cannot be tainted.
                                callee_sum.param_count = invoke->args.size();
                                callee_sum.return_dep =
                                        DepSet(invoke->args.size());
                            } else {
                                // Look up or compute the summary for exactly
                                // the taint pattern that arrives at this call.
                                callee_sum = get_or_compute_ctx(
                                        vm, tgt, cg, callee_ctx, cache,
                                        lib_policy, sinks, sink_hits);
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
                    }
                }
                else if (opcode_val == opcode::op_return
                         || opcode_val == opcode::op_return_object
                         || opcode_val == opcode::op_return_wide) {
                    sum.return_dep |= use_dep;
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
                        }
                    }
                    for (auto reg : DEF[i]) {
                        if (reg < new_out.size()) {
                            new_out[reg] = use_dep | field_dep;
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
                                && val_idx < new_in.size()
                                && new_in[val_idx].any()) {
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
                                    auto& ft = field_taint[map_key];
                                    if (ft.size() < sum.param_count) {
                                        ft.resize(sum.param_count);
                                    }
                                    auto old_ft = ft;
                                    ft |= new_in[val_idx];
                                    // Wide value (long/double) spans val_idx and
                                    // val_idx+1; include the high word's taint.
                                    if ((opcode_val == opcode::op_iput_wide
                                         || opcode_val == opcode::op_sput_wide)
                                        && val_idx + 1 < new_in.size()) {
                                        ft |= new_in[val_idx + 1];
                                    }
                                    if (ft != old_ft) {
                                        changed = true;
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
                    // Taint of the value register (vA) flows into the element
                    // taint slot for array register vB.
                    auto regs_view = regs(insn_obj);
                    auto rit = regs_view.begin();
                    if (rit != regs_view.end()) {
                        std::size_t val_idx;
                        if (normalize_reg(*rit, reg_domain, val_idx)) {
                            DepSet val_dep(sum.param_count);
                            if (val_idx < new_in.size()) {
                                val_dep |= new_in[val_idx];
                            }
                            // Wide value spans val_idx and val_idx+1.
                            if (opcode_val == opcode::op_aput_wide
                                && val_idx + 1 < new_in.size()) {
                                val_dep |= new_in[val_idx + 1];
                            }
                            if (val_dep.any()) {
                                ++rit; // advance to array register (vB)
                                if (rit != regs_view.end()) {
                                    std::size_t arr_idx;
                                    if (normalize_reg(*rit, reg_domain,
                                                      arr_idx)) {
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

                // At the method entry (no-predecessor instruction), the param
                // registers are "defined" by a synthetic binding instruction.
                // That DEF kill removes the param_seed taint we set in new_in.
                // Restore it: the analysis models parameters as tainted at entry,
                // so OR param_seed back into new_out unconditionally.
                if (!saw_pred) {
                    for (std::size_t r = 0; r < reg_domain; ++r) {
                        new_out[r] |= param_seed[r];
                    }
                }

                if (new_in != IN[i] || new_out != OUT[i]
                    || new_pending != pending[i]) {
                    IN[i] = std::move(new_in);
                    OUT[i] = std::move(new_out);
                    pending[i] = std::move(new_pending);
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
            CtxCache& cache,
            LibPolicy lib_policy,
            const std::vector<SinkSpec>& sinks,
            std::vector<SinkHit>& sink_hits)
    {
        CtxKey key{mid, ctx};

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
                                      cache, lib_policy, sinks, sink_hits);
            const auto& prev = cache.interim.at(key);
            const bool converged = (prev.return_dep == sum.return_dep
                                    && prev.field_write_deps == sum.field_write_deps);
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
                // ProcessBuilder: tainted command list or single string
                {"Ljava/lang/ProcessBuilder;", "<init>",
                 "([Ljava/lang/String;)V"},
                {"Ljava/lang/ProcessBuilder;", "<init>",
                 "(Ljava/util/List;)V"},

                // -------------------------------------------------------
                // File I/O — tainted file path written to/read from
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

                // -------------------------------------------------------
                // Network — tainted URL / hostname / port
                // -------------------------------------------------------
                {"Ljava/net/URL;", "<init>",
                 "(Ljava/lang/String;)V"},
                {"Ljava/net/Socket;", "<init>",
                 "(Ljava/lang/String;I)V"},
                {"Ljava/net/HttpURLConnection;", "connect", "()V"},

                // -------------------------------------------------------
                // Android logging — information disclosure via logcat
                // -------------------------------------------------------
                {"Landroid/util/Log;", "v",
                 "(Ljava/lang/String;Ljava/lang/String;)I"},
                {"Landroid/util/Log;", "d",
                 "(Ljava/lang/String;Ljava/lang/String;)I"},
                {"Landroid/util/Log;", "i",
                 "(Ljava/lang/String;Ljava/lang/String;)I"},
                {"Landroid/util/Log;", "w",
                 "(Ljava/lang/String;Ljava/lang/String;)I"},
                {"Landroid/util/Log;", "e",
                 "(Ljava/lang/String;Ljava/lang/String;)I"},
                {"Landroid/util/Log;", "wtf",
                 "(Ljava/lang/String;Ljava/lang/String;)I"},

                // Java standard logging
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
                 "(Ljava/lang/String;[Ljava/lang/String;)Landroid/database/Cursor;"},

                // -------------------------------------------------------
                // Android WebView — tainted URL or JS injected into WebView
                // -------------------------------------------------------
                {"Landroid/webkit/WebView;", "loadUrl",
                 "(Ljava/lang/String;)V"},
                {"Landroid/webkit/WebView;", "loadData",
                 "(Ljava/lang/String;Ljava/lang/String;Ljava/lang/String;)V"},
                {"Landroid/webkit/WebView;", "evaluateJavascript",
                 "(Ljava/lang/String;Landroid/webkit/ValueCallback;)V"},

                // -------------------------------------------------------
                // SMS — tainted phone number or message body
                // -------------------------------------------------------
                {"Landroid/telephony/SmsManager;", "sendTextMessage",
                 "(Ljava/lang/String;Ljava/lang/String;Ljava/lang/String;"
                 "Landroid/app/PendingIntent;Landroid/app/PendingIntent;)V"},

                // -------------------------------------------------------
                // JNDI — tainted lookup name (Log4Shell-style)
                // -------------------------------------------------------
                {"Ljavax/naming/InitialContext;", "lookup",
                 "(Ljava/lang/String;)Ljava/lang/Object;"},
                {"Ljavax/naming/directory/InitialDirContext;", "search",
                 "(Ljava/lang/String;Ljava/lang/String;"
                 "Ljavax/naming/directory/SearchControls;)"
                 "Ljavax/naming/NamingEnumeration;"},

                // -------------------------------------------------------
                // Reflection — tainted class/method name loaded dynamically
                // -------------------------------------------------------
                {"Ljava/lang/Class;", "forName",
                 "(Ljava/lang/String;)Ljava/lang/Class;"},
                {"Ljava/lang/ClassLoader;", "loadClass",
                 "(Ljava/lang/String;)Ljava/lang/Class;"},

                // -------------------------------------------------------
                // Inter-App Communication — tainted data leaving the app
                // -------------------------------------------------------
                // Broadcast: Intent sent to registered broadcast receivers
                // (potentially in other apps). sendBroadcast/sendOrdered are
                // inter-app by design — unlike putExtra/startActivity they
                // are not used for intra-app navigation or Fragment args.
                {"Landroid/content/Context;", "sendBroadcast",
                 "(Landroid/content/Intent;)V"},
                {"Landroid/content/Context;", "sendOrderedBroadcast",
                 "(Landroid/content/Intent;Ljava/lang/String;)V"},
        };
    }
}

InterprocParamResult run_interproc_param_taint(virtual_machine& vm,
                                               const InterprocParamConfig& config)
{
    InterprocParamResult result;
    auto cg = build_call_graph(vm);
    auto sinks = config.sinks.empty() ? default_sinks() : config.sinks;

    auto is_source_method = [&](const MethodId& mid,
                                const method_vertex_descriptor& mv) {
        if (!config.source_methods.empty()) {
            return std::find(config.source_methods.begin(),
                             config.source_methods.end(),
                             mid)
                    != config.source_methods.end();
        }
        if (config.seed_public_only) {
            return (vm.methods()[mv].access_flags & acc_public) != 0;
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

        auto sum = get_or_compute_ctx(vm, mid, cg, entry_ctx, cache,
                                      config.lib_policy, sinks,
                                      result.sink_hits);

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

    return result;
}

} // namespace dfa
} // namespace analysis
} // namespace jitana
