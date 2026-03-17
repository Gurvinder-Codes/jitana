# Variable Reuse Analysis Overview

This note summarizes the intraprocedural variable reuse analysis and how the CLI exercises it (`tools/jitana-dfa`).

## Files and Entry Points

| File | Purpose |
| --- | --- |
| `include/jitana/analysis/variable_reuse.hpp` | Public API exposing `ReuseResult` and `run_variable_reuse(virtual_machine&, method_vertex_descriptor, const LivenessResult&)` |
| `lib/jitana/analysis/variable_reuse.cpp` | Implementation that derives live ranges from liveness and finds disjoint register pairs |
| `tools/jitana-dfa/main.cpp` | Runs the analysis for each method and prints reuse candidates |

## ReuseResult surface

```cpp
struct ReuseResult {
    std::size_t reg_domain;
    std::vector<std::pair<int,int>> live_ranges; // [first,last] per register
    std::vector<ReusePair> disjoint_pairs;       // non-overlapping live ranges
};
```

* `reg_domain` matches the method’s register count.
* `live_ranges[r]` captures the first/last instruction index where register `r` is live (`-1/-1` if never live).
* `disjoint_pairs` lists register pairs whose live ranges do not overlap and could share a slot.

## Algorithm (lib/jitana/analysis/variable_reuse.cpp)

1. **Live ranges**  
   Convert liveness bitsets into coarse ranges `[first,last]` for each register, ignoring unused registers.
2. **Pair search**  
   For every register pair `(r1, r2)`, if both are used and their ranges are disjoint, emit a `ReusePair` note.

No CFG traversal is needed beyond the liveness precomputation.

## CLI (tools/jitana-dfa/main.cpp)

For each method with code, after running liveness:
```cpp
auto reuse = analysis::dfa::run_variable_reuse(vm, mv, L);
```
The CLI prints the register domain, the number of disjoint pairs, and each candidate pair with a short note.
