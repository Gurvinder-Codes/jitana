#pragma once

#include <cstddef>
#include <string>
#include <unordered_map>
#include <vector>

#include <boost/dynamic_bitset.hpp>

#include <jitana/vm_core/hdl.hpp>
#include <jitana/vm_core/virtual_machine.hpp>
#include <jitana/vm_graph/method_graph.hpp>

namespace jitana {
namespace analysis {
namespace dfa {

// Simple identifiers used to keep summaries stable.
struct MethodId {
    jvm_type_hdl type;
    std::string name;
    std::string descriptor;

    MethodId() = default;
    MethodId(jvm_type_hdl type, std::string name, std::string descriptor);
};

struct MethodIdHash {
    std::size_t operator()(const MethodId& id) const;
};

bool operator==(const MethodId& a, const MethodId& b);
bool operator!=(const MethodId& a, const MethodId& b);

struct CallSiteId {
    MethodId caller;
    uint32_t offset;
};

struct CallSiteIdHash {
    std::size_t operator()(const CallSiteId& cs) const;
};

bool operator==(const CallSiteId& a, const CallSiteId& b);

struct MethodSummary {
    boost::dynamic_bitset<> return_dep;
    std::size_t param_count{0};
    // Fields written by this method with parameter-derived taint.
    // Key:   JVM-level field descriptor "Ltype;.name:Ftype;"
    // Value: which of this method's params can taint the field.
    std::unordered_map<std::string, boost::dynamic_bitset<>> field_write_deps;
};

struct SinkSpec {
    std::string type_descriptor;
    std::string name;
    std::string descriptor;
};

struct SinkHit {
    MethodId caller;
    uint32_t offset{0};
    MethodId callee;
    std::vector<std::size_t> tainted_args;
};

enum class LibPolicy { Conservative, Optimistic };

struct InterprocParamConfig {
    LibPolicy lib_policy{LibPolicy::Conservative};
    // If empty, defaults to seeding all methods (overridden by flags below);
    // otherwise, only the listed methods seed their parameters.
    std::vector<MethodId> source_methods;
    bool seed_public_only{false}; // Set true to seed only public methods.
    std::vector<SinkSpec> sinks; // Optional: leave empty to use defaults.
};

struct InterprocParamResult {
    std::unordered_map<MethodId, MethodSummary, MethodIdHash> summaries;
    std::vector<SinkHit> sink_hits;
};

// Compute context-insensitive parameter-to-return summaries across methods.
InterprocParamResult run_interproc_param_taint(
        virtual_machine& vm,
        const InterprocParamConfig& config = InterprocParamConfig{});

// Helper to build MethodId from an existing JVM handle.
MethodId make_method_id(const jvm_method_hdl& hdl);

} // namespace dfa
} // namespace analysis
} // namespace jitana
