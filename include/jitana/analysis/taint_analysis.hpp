#pragma once

#include <cstddef>
#include <vector>

#include <boost/dynamic_bitset.hpp>

#include <jitana/jitana.hpp>

namespace jitana {
namespace analysis {
namespace dfa {

struct TaintResult {
    // Order of Instruction analyzed.
    std::vector<insn_vertex_descriptor> order;

    // TAINT_IN[i] / TAINT_OUT[i] correspond to order[i].
    std::vector<boost::dynamic_bitset<>> TAINT_IN;
    std::vector<boost::dynamic_bitset<>> TAINT_OUT;

    // Number of virtual registers considered.
    std::size_t reg_domain{0};
};

TaintResult run_taint(::jitana::virtual_machine& vm,
                      const method_vertex_descriptor& mv);

}
}
}
