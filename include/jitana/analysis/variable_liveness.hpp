#pragma once

#include <vector>
#include <cstddef>
#include <boost/dynamic_bitset.hpp>

#include <jitana/jitana.hpp>

namespace jitana {
namespace analysis {
namespace dfa {

struct LivenessResult {
    // Order of Instruction analyzed.
    std::vector<insn_vertex_descriptor> order;

    // LIVE_IN[i] / LIVE_OUT[i] correspond to order[i].
    std::vector<boost::dynamic_bitset<>> LIVE_IN;
    std::vector<boost::dynamic_bitset<>> LIVE_OUT;

    // Number of virtual registers considered.
    std::size_t reg_domain{0};
};

LivenessResult run_liveness(::jitana::virtual_machine& vm,
                            const method_vertex_descriptor& mv);

} // namespace dfa
} // namespace analysis
} // namespace jitana
