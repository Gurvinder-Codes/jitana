# Taint Analysis Overview

This note describes the intraprocedural and interprocedural taint analysis in Jitana and how the DFA CLI reports it.

## Files and Entry Points

| File | Purpose |
| --- | --- |
| `include/jitana/analysis/taint_analysis.hpp` | Public API for intraprocedural taint: `TaintResult`, `run_taint(vm, method)` |
| `lib/jitana/analysis/taint_analysis.cpp` | Implementation of the forward taint data-flow |
| `include/jitana/analysis/interproc_param_taint.hpp` | Public API for interprocedural param taint: `InterprocParamResult`, `run_interproc_param_taint(vm, config)` |
| `lib/jitana/analysis/interproc_param_taint.cpp` | Context-insensitive parameter-to-return summaries and sink detection |
| `tools/jitana-dfa/main.cpp` | Runs intra- and interprocedural taint and prints results (optionally writes a DOT graph) |

## TaintResult surface

```cpp
struct TaintResult {
    std::vector<insn_vertex_descriptor> order;
    std::vector<boost::dynamic_bitset<>> TAINT_IN;
    std::vector<boost::dynamic_bitset<>> TAINT_OUT;
    std::size_t reg_domain{0};
};
```

* `order` is the analyzed instruction order (indices into the method’s insn graph).
* `TAINT_IN[i]` / `TAINT_OUT[i]` correspond to `order[i]`.
* `reg_domain` matches the method’s register count.

## Semantics (lib/jitana/analysis/taint_analysis.cpp)

* **Sources**: All incoming parameter registers (`ins_size` highest registers) start tainted.
* **Propagation**: Forward over the CFG.
  * `TAINT_IN[v]` is the union of predecessors’ `TAINT_OUT`; if no predecessors, seed with parameter taint.
  * Start `TAINT_OUT` as `TAINT_IN`, then clear any registers defined by the instruction (overwrite kills).
  * If any used register is tainted in `TAINT_IN`, mark all defined registers tainted in `TAINT_OUT`.
* **Normalization**: Ignores pseudo registers (`result`, `exception`) and any negative/invalid indices.
* **Fixpoint**: Iterate until `TAINT_IN`/`TAINT_OUT` stabilize.

This is intraprocedural and register-scoped; it does not model heap, fields, returns, or sanitizers beyond overwrite.

## Interprocedural parameter taint

* **Summaries**: For each method, which parameter indices the return value depends on (`return_dep`). Built with a context-insensitive fixpoint over the call graph.
* **Sources**: By default, all methods have their parameters seeded as tainted. Set `seed_public_only = true` to restrict seeding to public methods only, or populate `source_methods` to seed a specific list of methods.
* **Sinks**: Optional list of (type, name, descriptor) specs; if empty, a default set is used (e.g. `Runtime.exec`, `Log.d`, `Socket.<init>`, etc.). When tainted arguments reach a sink, a `SinkHit` is recorded.
* **Library policy**: Unresolved or missing callees can be treated as `Conservative` (return depends on all args) or `Optimistic` (return depends on none).

The tool prints interprocedural summaries (public methods with non-empty `ReturnDependsOn`) and all sink hits. With `--taint-graph FILE`, it writes a DOT digraph of caller→sink edges (tainted arg indices and bytecode offsets).

## CLI (tools/jitana-dfa)

**Usage:**
```text
jitana-dfa [--interproc-only] [--taint-graph taint.dot] <file.dex | app.apk>
```

* `--interproc-only`: Run only interprocedural taint; print summaries and sink hits (and write graph if `--taint-graph` is given). Skip per-method intraprocedural taint output.
* `--taint-graph FILE`: Write a DOT file showing taint flows from callers to sink methods (red nodes = sinks, edges labeled with tainted arg indices and offsets).

**Intraprocedural:** For each method with code (when not using `--interproc-only`), the CLI runs `run_taint(vm, mv)` and prints the register domain and which registers are tainted (union of TAINT_IN/TAINT_OUT), for methods that have both taint and at least one tainted use.

**Interprocedural:** Always runs `run_interproc_param_taint(vm, config)` and prints:
1. Method summaries: public methods whose return depends on one or more parameters (`ReturnDependsOn = { param indices }`).
2. Tainted sink hits: each call site where tainted arguments reach a sink, with caller, callee, offset, and tainted argument indices.
