#pragma once

#include <cstddef>
#include <string>
#include <unordered_map>
#include <unordered_set>
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
    // True if this method (or any callee it reaches) can return a value that
    // is derived from a known source API (getDeviceId, getLastKnownLocation,
    // etc.).  Used to propagate source-taint across method boundaries.
    bool src_return_dep{false};
    // Best-effort identity of the source API that makes src_return_dep true.
    // Empty if unknown (e.g. propagated through a callee chain without origin).
    MethodId src_return_origin;
    // Fields written by this method with source-API-derived taint.
    // Keys use the same "P{param_idx}:{fkey}" / "STATIC:{fkey}" convention
    // as field_write_deps, enabling cross-lifecycle and cross-method
    // source-taint propagation without touching the param-taint domain.
    std::unordered_set<std::string> source_field_writes;
};

struct SinkSpec {
    std::string type_descriptor;
    std::string name;
    std::string descriptor;
};

struct SourceSpec {
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

// A SourceHit records a call site where the return value of a known source API
// flows into a known sink argument.
struct SourceHit {
    MethodId caller;        // Method containing both the source call and sink call
    uint32_t source_offset{0}; // Bytecode offset of the source API call
    MethodId source_callee; // The source API invoked
    uint32_t sink_offset{0};   // Bytecode offset of the sink API call
    MethodId sink_callee;   // The sink API that received source-tainted data
    std::vector<std::size_t> tainted_args; // Which sink args carry source data
};

enum class LibPolicy { Conservative, Optimistic };

struct InterprocParamConfig {
    LibPolicy lib_policy{LibPolicy::Conservative};
    // If empty, defaults to seeding all methods (overridden by flags below);
    // otherwise, only the listed methods seed their parameters.
    std::vector<MethodId> source_methods;
    bool seed_public_only{false}; // Set true to seed only public methods.
    // Don't seed private methods that have no incoming call-graph edges.
    // These are unreachable dead code (no caller can invoke them).
    bool skip_private_no_callers{false};
    std::vector<SinkSpec> sinks;    // Optional: leave empty to use defaults.
    std::vector<SourceSpec> sources; // Optional: leave empty to use defaults.
    // Class descriptor prefixes (e.g. "Landroid/support/") whose methods are
    // excluded from param-taint seeding. Does NOT affect source-to-sink
    // detection. Leave empty to seed all methods (default / backward-compat).
    std::vector<std::string> param_seed_exclude_prefixes;
    // Model Android component lifecycle ordering so that source-tainted data
    // stored to instance fields in one callback (e.g. onCreate) is visible in
    // later callbacks of the same component (e.g. onResume).  Default: true.
    bool model_android_lifecycle{true};
};

struct InterprocParamResult {
    std::unordered_map<MethodId, MethodSummary, MethodIdHash> summaries;
    std::vector<SinkHit> sink_hits;
    std::vector<SourceHit> source_sink_hits; // Source-API-return → sink flows
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
