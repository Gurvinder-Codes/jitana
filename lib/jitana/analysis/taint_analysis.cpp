#include "jitana/analysis/taint_analysis.hpp"

#include <algorithm>
#include <cstdint>
#include <vector>

namespace jitana {
namespace analysis {
namespace dfa {
namespace {
    // Build a stable order over the instruction graph vertices.
    static std::vector<insn_vertex_descriptor>
    build_order(const insn_graph& ig)
    {
        std::vector<insn_vertex_descriptor> order;
        order.reserve(num_vertices(ig));
        for (auto it = vertices(ig); it.first != it.second; ++it.first) {
            order.push_back(*it.first);
        }
        return order;
    }

    // Normalize register_idx into a register domain offset if possible.
    inline bool normalize_reg(const register_idx& reg,
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
}

TaintResult run_taint(::jitana::virtual_machine& vm,
                      const method_vertex_descriptor& mv)
{
    const auto& mg = vm.methods();
    const auto& ig = mg[mv].insns;

    TaintResult R;
    R.order = build_order(ig);
    R.reg_domain = ig[boost::graph_bundle].registers_size;

    if (R.order.empty()) {
        return R;
    }

    const std::size_t n = R.order.size();

    auto make_bitset = [&](std::size_t bits) {
        return boost::dynamic_bitset<>(bits);
    };

    R.TAINT_IN.assign(n, make_bitset(R.reg_domain));
    R.TAINT_OUT.assign(n, make_bitset(R.reg_domain));

    // Precompute filtered defs/uses for each instruction.
    std::vector<std::vector<std::size_t>> DEF(n);
    std::vector<std::vector<std::size_t>> USE(n);

    for (std::size_t i = 0; i < n; ++i) {
        const auto& insn = ig[R.order[i]].insn;

        for (const auto& reg : defs(insn)) {
            std::size_t idx;
            if (normalize_reg(reg, R.reg_domain, idx)) {
                DEF[i].push_back(idx);
            }
        }
        for (const auto& reg : uses(insn)) {
            std::size_t idx;
            if (normalize_reg(reg, R.reg_domain, idx)) {
                USE[i].push_back(idx);
            }
        }

        auto dedup = [](auto& vec) {
            std::sort(begin(vec), end(vec));
            vec.erase(std::unique(begin(vec), end(vec)), end(vec));
        };
        dedup(DEF[i]);
        dedup(USE[i]);
    }

    const auto vertex_count = static_cast<std::size_t>(num_vertices(ig));
    std::vector<std::size_t> index_of(vertex_count, n);
    for (std::size_t i = 0; i < n; ++i) {
        if (R.order[i] < index_of.size()) {
            index_of[R.order[i]] = i;
        }
    }

    // Seed taint with incoming parameters (ins registers live at the end).
    boost::dynamic_bitset<> param_taint(R.reg_domain);
    const auto ins_size = ig[boost::graph_bundle].ins_size;
    if (ins_size <= R.reg_domain) {
        const auto start = R.reg_domain - ins_size;
        for (std::size_t r = start; r < R.reg_domain; ++r) {
            param_taint.set(r);
        }
    }

    bool changed = true;
    while (changed) {
        changed = false;
        for (std::size_t i = 0; i < n; ++i) {
            const auto v = R.order[i];

            auto new_in = make_bitset(R.reg_domain);
            bool saw_pred = false;
            for (auto ee = in_edges(v, ig); ee.first != ee.second; ++ee.first) {
                auto pred = source(*ee.first, ig);
                if (pred < index_of.size()) {
                    auto pred_idx = index_of[pred];
                    if (pred_idx < n) {
                        new_in |= R.TAINT_OUT[pred_idx];
                        saw_pred = true;
                    }
                }
            }
            if (!saw_pred && param_taint.any()) {
                new_in |= param_taint;
            }

            auto new_out = new_in;

            // Kill overwritten registers.
            for (auto reg : DEF[i]) {
                if (reg < new_out.size()) {
                    new_out.reset(reg);
                }
            }

            // Propagate taint from tainted uses into defs.
            bool tainted_use = false;
            for (auto reg : USE[i]) {
                if (reg < new_in.size() && new_in.test(reg)) {
                    tainted_use = true;
                    break;
                }
            }
            if (tainted_use) {
                for (auto reg : DEF[i]) {
                    if (reg < new_out.size()) {
                        new_out.set(reg);
                    }
                }
            }

            if (new_in != R.TAINT_IN[i] || new_out != R.TAINT_OUT[i]) {
                R.TAINT_IN[i] = std::move(new_in);
                R.TAINT_OUT[i] = std::move(new_out);
                changed = true;
            }
        }
    }

    return R;
}

} 
} 
} 
