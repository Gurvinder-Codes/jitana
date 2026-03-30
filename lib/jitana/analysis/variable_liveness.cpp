#include "jitana/analysis/variable_liveness.hpp"

#include <algorithm>
#include <cstdint>
#include <utility>
#include <vector>

namespace jitana {
namespace analysis {
namespace dfa {

namespace {
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
}

LivenessResult run_liveness(::jitana::virtual_machine& vm,
                            const method_vertex_descriptor& mv)
{
    const auto& mg = vm.methods();
    const auto& ig = mg[mv].insns;

    // Construct analysis result skeleton.
    LivenessResult R;
    R.order = build_order(ig);

    const std::size_t n = R.order.size();

    R.reg_domain = ig[boost::graph_bundle].registers_size;

    auto make_bitset = [&](std::size_t bits) {
        return boost::dynamic_bitset<>(bits);
    };

    R.LIVE_IN.assign(n, make_bitset(R.reg_domain));
    R.LIVE_OUT.assign(n, make_bitset(R.reg_domain));

    std::vector<boost::dynamic_bitset<>> USE(n, make_bitset(R.reg_domain));
    std::vector<boost::dynamic_bitset<>> DEF(n, make_bitset(R.reg_domain));

    const auto vertex_count = static_cast<std::size_t>(num_vertices(ig));
    std::vector<std::size_t> index_of(vertex_count, n);
    for (std::size_t i = 0; i < n; ++i) {
        if (R.order[i] < index_of.size()) {
            index_of[R.order[i]] = i;
        }
    }

    auto add_regs = [&](boost::dynamic_bitset<>& bits,
                        const std::vector<register_idx>& regs) {
        for (const auto& reg : regs) {
            if (!reg.valid() || reg.is_result() || reg.is_exception()) {
                continue;
            }
            const auto raw = static_cast<int32_t>(reg);
            if (raw < 0) {
                continue;
            }
            const auto idx = static_cast<std::size_t>(raw);
            if (idx >= R.reg_domain) {
                continue;
            }
            bits.set(idx);
        }
    };

    for (std::size_t i = 0; i < n; ++i) {
        const auto& insn = ig[R.order[i]].insn;
        add_regs(DEF[i], defs(insn));
        add_regs(USE[i], uses(insn));
    }

    bool changed = true;
    while (changed) {
        changed = false;
        for (std::size_t idx_rev = n; idx_rev-- > 0;) {
            const auto i = idx_rev;

            auto new_out = make_bitset(R.reg_domain);
            for (auto ee = out_edges(R.order[i], ig); ee.first != ee.second;
                 ++ee.first) {
                auto succ = target(*ee.first, ig);
                if (succ < index_of.size()) {
                    auto succ_idx = index_of[succ];
                    if (succ_idx < n) {
                        new_out |= R.LIVE_IN[succ_idx];
                    }
                }
            }

            if (new_out != R.LIVE_OUT[i]) {
                R.LIVE_OUT[i] = new_out;
                changed = true;
            }

            auto live_out_minus_def = R.LIVE_OUT[i];
            live_out_minus_def &= ~DEF[i];
            auto new_in = USE[i];
            new_in |= live_out_minus_def;
            if (new_in != R.LIVE_IN[i]) {
                R.LIVE_IN[i] = new_in;
                changed = true;
            }
        }
    }

    return R;
}

} // namespace dfa
} // namespace analysis
} // namespace jitana
