#pragma once

#include <vector>
#include <string>
#include <utility>

#include <jitana/vm_core/virtual_machine.hpp>
#include <jitana/vm_graph/method_graph.hpp>
#include <jitana/analysis/variable_liveness.hpp>

namespace jitana {
namespace analysis {
namespace dfa {

    /// Pair: two registers whose live ranges do not overlap.
    struct ReusePair {
        int reg_a;          
        int reg_b;          
        std::string note;  
    };

    /// Summary of variable reuse opportunities for a single method.
    struct ReuseResult {
        std::size_t reg_domain{0};                      
        std::vector<std::pair<int,int>> live_ranges;
        std::vector<ReusePair> disjoint_pairs;
    };

    ReuseResult run_variable_reuse(::jitana::virtual_machine& vm,
                                   const ::jitana::method_vertex_descriptor& mv,
                                   const LivenessResult& L);

} 
} 
}
