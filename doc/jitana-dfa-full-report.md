# JITANA-DFA: Full Technical Report

> **Branch:** `jitana-dfa`  
> **Scope of changes:** New analysis passes, a new CLI tool, and visualization infrastructure added on top of the existing JITANA framework.

---

## Table of Contents

1. [Overview of Changes](#1-overview-of-changes)
2. [File Map](#2-file-map)
3. [Variable Liveness Analysis](#3-variable-liveness-analysis)
4. [Variable Reuse Analysis](#4-variable-reuse-analysis)
5. [Intraprocedural Taint Analysis](#5-intraprocedural-taint-analysis)
6. [Interprocedural Parameter Taint Analysis](#6-interprocedural-parameter-taint-analysis)
   - 6.1 [Data Structures and API](#61-data-structures-and-api)
   - 6.2 [Call Graph Construction](#62-call-graph-construction)
   - 6.3 [Taint Domain](#63-taint-domain)
   - 6.4 [Intra-Method Dataflow Pass](#64-intra-method-dataflow-pass)
   - 6.5 [Transfer Functions — Full Instruction Coverage](#65-transfer-functions--full-instruction-coverage)
   - 6.6 [Context-Sensitive Summary Memoization (CtxCache)](#66-context-sensitive-summary-memoization-ctxcache)
   - 6.7 [Source-to-Sink Tracking](#67-source-to-sink-tracking)
   - 6.8 [Sink Specification and Subtype Matching](#68-sink-specification-and-subtype-matching)
   - 6.9 [Library Exclusion](#69-library-exclusion)
7. [Inter-App IPC Chain Detection](#7-inter-app-ipc-chain-detection)
8. [The `jitana-dfa` CLI Tool](#8-the-jitana-dfa-cli-tool)
   - 8.1 [Input Handling (DEX and APK)](#81-input-handling-dex-and-apk)
   - 8.2 [Bootstrap Loader and Placeholder Classes](#82-bootstrap-loader-and-placeholder-classes)
   - 8.3 [Intraprocedural Phase](#83-intraprocedural-phase)
   - 8.4 [Interprocedural Phase](#84-interprocedural-phase)
   - 8.5 [Output and Reporting](#85-output-and-reporting)
9. [DOT Graph Visualization](#9-dot-graph-visualization)
   - 9.1 [Two-Level Layout (Single App)](#91-two-level-layout-single-app)
   - 9.2 [Four-Level Layout (Inter-App Chains)](#92-four-level-layout-inter-app-chains)
10. [Key Algorithmic Challenges and Solutions](#10-key-algorithmic-challenges-and-solutions)
11. [Known Sink Set](#11-known-sink-set)
12. [Building and Running](#12-building-and-running)

---

## 1. Overview of Changes

The `jitana-dfa` branch adds a complete static taint analysis pipeline to the JITANA framework. The work is organized into four analysis passes and one CLI driver:

| Pass | Kind | What it computes |
|---|---|---|
| Variable Liveness | Intraprocedural | `LIVE_IN[i]` / `LIVE_OUT[i]` per instruction |
| Variable Reuse | Intraprocedural | Register pairs with non-overlapping live ranges |
| Taint Analysis | Intraprocedural | `TAINT_IN[i]` / `TAINT_OUT[i]` per instruction |
| Parameter Taint | Interprocedural | Per-method summaries + sink hits + source-sink flows |

All four passes are exercised by the `tools/jitana-dfa` binary, which can load a single `.dex` file or a full `.apk`, run every pass over every method, and optionally write a GraphViz DOT taint flow graph.

---

## 2. File Map

```
include/jitana/analysis/
  variable_liveness.hpp        — LivenessResult, run_liveness()
  variable_reuse.hpp           — ReuseResult, run_variable_reuse()
  taint_analysis.hpp           — TaintResult, run_taint()
  interproc_param_taint.hpp    — MethodSummary, InterprocParamResult,
                                  run_interproc_param_taint()

lib/jitana/analysis/
  variable_liveness.cpp        — Backward dataflow fixed-point
  variable_reuse.cpp           — Live-range extraction + disjoint pair search
  taint_analysis.cpp           — Forward taint fixed-point (intraprocedural)
  interproc_param_taint.cpp    — Context-sensitive interprocedural analysis

tools/jitana-dfa/
  main.cpp                     — CLI driver: input parsing, loader wiring,
                                  per-method passes, output, DOT generation
```

---

## 3. Variable Liveness Analysis

### Purpose

Liveness analysis determines, for each program point, which virtual registers hold a value that *may be read* before being overwritten. It is used in JITANA-DFA both as a utility consumed by Variable Reuse Analysis and as diagnostic output in the CLI.

### API

```cpp
// include/jitana/analysis/variable_liveness.hpp
struct LivenessResult {
    std::vector<insn_vertex_descriptor> order; // instruction visit order
    std::vector<boost::dynamic_bitset<>> LIVE_IN;
    std::vector<boost::dynamic_bitset<>> LIVE_OUT;
    std::size_t reg_domain{0};
};

LivenessResult run_liveness(virtual_machine& vm,
                            method_vertex_descriptor mv);
```

`LIVE_IN[i]` and `LIVE_OUT[i]` correspond to `order[i]`. The bitset width equals the method's `registers_size` from the DEX code item.

### Algorithm

The implementation follows the classical backward dataflow equations:

```
LIVE_OUT[i] = ⋃  LIVE_IN[s]   for each control-flow successor s of i
LIVE_IN[i]  = USE[i] ∪ (LIVE_OUT[i] \ DEF[i])
```

**Step 1 — Build instruction order.**  
`build_order` copies the instruction graph's vertex descriptors into a flat vector. No special topological sort is required; any consistent enumeration converges.

**Step 2 — Compute USE and DEF sets.**  
For each instruction, `defs(insn)` and `uses(insn)` (from `insn.hpp`) return the set of registers written and read respectively. A helper `add_regs` filters out pseudo-registers (`result`, `exception`) and negative/out-of-range indices so only real virtual registers (`v0` … `vN`) are tracked.

**Step 3 — Fixed-point iteration.**  
Iterates in reverse order until no bitset changes. `boost::dynamic_bitset` provides compact storage and fast bitwise operations, which keeps the inner loop efficient even for methods with large register files.

**Step 4 — Return result.**  
The stable `LIVE_IN`, `LIVE_OUT`, and `order` vectors are returned. No JITANA graph data is mutated.

### CLI Output Sample

```
[+] Method #2: 100:LSimpleTest;.main([Ljava/lang/String;)V
    Instructions analyzed: 15
    Register domain size : 4
    [insn#7] LIVE_IN: v0 v1 v3  | LIVE_OUT: v0 v1 v2 v3
```

---

## 4. Variable Reuse Analysis

### Purpose

Variable Reuse Analysis identifies pairs of virtual registers whose live ranges do not overlap. Such pairs are candidates for register coalescing — the two registers could share one slot without affecting correctness. This is primarily a program-optimization diagnostic.

### API

```cpp
// include/jitana/analysis/variable_reuse.hpp
struct ReusePair { int r1; int r2; };

struct ReuseResult {
    std::size_t reg_domain;
    std::vector<std::pair<int,int>> live_ranges; // [first, last] per register
    std::vector<ReusePair> disjoint_pairs;       // non-overlapping candidates
};

ReuseResult run_variable_reuse(virtual_machine& vm,
                               method_vertex_descriptor mv,
                               const LivenessResult& liveness);
```

`live_ranges[r]` holds `{first, last}` — the first and last instruction index (in `liveness.order`) where register `r` is live. A value of `{-1, -1}` means the register is never live.

### Algorithm

**Step 1 — Live range extraction.**  
Walk `LIVE_IN` and `LIVE_OUT`. For each register `r`, record the smallest instruction index where it is live (`first`) and the largest (`last`).

**Step 2 — Disjoint pair search.**  
For every pair `(r1, r2)` where both are used: if `last[r1] < first[r2]` or `last[r2] < first[r1]`, the ranges are disjoint and a `ReusePair` is emitted. No CFG traversal is needed; the live-range precomputation already captures the necessary information.

### CLI Output Sample

```
[+] Method #3: 100:LSimpleTest;.process(Ljava/lang/String;)V
    Register domain: 6
    Disjoint reuse pairs (2):
      v2 and v5 do not overlap — could share a register slot
      v3 and v4 do not overlap — could share a register slot
```

---

## 5. Intraprocedural Taint Analysis

### Purpose

The intraprocedural taint analysis answers: *given that all parameters of a method are tainted at entry, which registers are tainted at each program point?* It is a fast, per-method pass used as a pre-filter in the CLI to identify methods that propagate taint to at least one use site.

### API

```cpp
// include/jitana/analysis/taint_analysis.hpp
struct TaintResult {
    std::vector<insn_vertex_descriptor> order;
    std::vector<boost::dynamic_bitset<>> TAINT_IN;
    std::vector<boost::dynamic_bitset<>> TAINT_OUT;
    std::size_t reg_domain{0};
};

TaintResult run_taint(virtual_machine& vm, method_vertex_descriptor mv);
```

Each bitset has width `reg_domain`. `TAINT_IN[i].test(r) = true` means register `r` is tainted immediately *before* instruction `order[i]` executes.

### Algorithm

This is a forward dataflow analysis.

**Sources.**  
All parameter registers are tainted at method entry. Dalvik stores parameters in the *highest* `ins_size` registers of the register file, i.e. registers `registers_size − ins_size` through `registers_size − 1`.

**Propagation equations.**  
```
TAINT_IN[i]  = ⋃ TAINT_OUT[pred]   for each predecessor pred of i
               (seed with param taint if no predecessors)

TAINT_OUT[i] = (TAINT_IN[i] \ kill[i]) ∪ gen[i]
```

where:
- `kill[i]` = set of registers *defined* by instruction `i` (overwrite kills previous taint).
- `gen[i]` = all registers *defined* by instruction `i`, if *any* used register is tainted in `TAINT_IN[i]`.

This is a conservative, use-def transfer: if any input is tainted, all outputs are considered tainted.

**Normalization.**  
Pseudo-registers (`result`, `exception`) and negative/invalid register indices are ignored throughout.

**Fixed-point.**  
Iterates (forward) until `TAINT_IN`/`TAINT_OUT` stabilize.

**Limitations.**  
- Intraprocedural only — no cross-method propagation.
- Binary (tainted / not tainted) — no source labeling.
- No heap, field, or array modeling; field-write taint is not tracked.

The interprocedural analysis (Section 6) removes all of these limitations.

### CLI Usage in Pre-filtering

The CLI runs `run_taint` for each method and skips printing unless:
1. The union of all `TAINT_IN` and `TAINT_OUT` is non-empty (taint exists somewhere), **and**
2. At least one tainted register is used by some instruction (i.e., taint reaches an actual use site).

This suppresses output for methods where parameters are defined but never read.

---

## 6. Interprocedural Parameter Taint Analysis

The interprocedural pass is the core contribution of JITANA-DFA. It computes whole-program *method summaries* that record, for each method, which input parameters can influence the return value and which parameters reach known dangerous sinks.

### 6.1 Data Structures and API

```cpp
// include/jitana/analysis/interproc_param_taint.hpp

struct MethodId {
    jvm_type_hdl type;       // declaring class descriptor + loader
    std::string name;        // method name
    std::string descriptor;  // JVM method descriptor "(params)return"
};

struct MethodSummary {
    boost::dynamic_bitset<> return_dep;  // param i → return value
    std::size_t param_count{0};
    // field_write_deps: fields written with param-derived taint.
    // Key forms:
    //   "P{k}:{Ltype;.name:Ftype;}"  — instance field on param k's object
    //   "STATIC:{Ltype;.name:Ftype;}"— static field
    std::unordered_map<std::string, boost::dynamic_bitset<>> field_write_deps;
};

struct SinkHit {
    MethodId caller;
    uint32_t offset;                      // bytecode offset of the call
    MethodId callee;                      // the sink method
    std::vector<std::size_t> tainted_args;// 0-based argument indices
};

struct SourceHit {
    MethodId caller;
    uint32_t source_offset;
    MethodId source_callee;               // source API invoked
    uint32_t sink_offset;
    MethodId sink_callee;                 // sink that received source data
    std::vector<std::size_t> tainted_args;
};

struct InterprocParamConfig {
    LibPolicy lib_policy{LibPolicy::Conservative};
    std::vector<MethodId> source_methods; // override for which methods to seed
    bool seed_public_only{false};
    std::vector<SinkSpec> sinks;          // override default sink set
    std::vector<SourceSpec> sources;      // optional source API set
    std::vector<std::string> param_seed_exclude_prefixes; // library exclusion
};

struct InterprocParamResult {
    std::unordered_map<MethodId, MethodSummary, MethodIdHash> summaries;
    std::vector<SinkHit> sink_hits;
    std::vector<SourceHit> source_sink_hits;
};

InterprocParamResult run_interproc_param_taint(
    virtual_machine& vm,
    const InterprocParamConfig& config = InterprocParamConfig{});
```

### 6.2 Call Graph Construction

Before any dataflow work, JITANA-DFA builds an explicit call graph over all loaded methods.

```cpp
struct CallGraph {
    unordered_map<MethodId, method_vertex_descriptor> method_vertices;
    unordered_map<CallSiteId, vector<MethodId>>       callees;  // site → targets
    unordered_map<MethodId, vector<CallSiteId>>       callers;  // method → call sites in it
    unordered_map<MethodId, vector<CallSiteId>>       outgoing; // method → its call sites
};
```

**Process:**
1. `add_call_graph_edges(vm)` is called first to populate JITANA's method graph with typed call edges (both direct and virtual).
2. JITANA-DFA iterates over all method vertices and their out-edges.
3. For each `method_call_edge_property` edge:
   - **Direct/static/super calls**: the statically declared target is used as-is.
   - **Virtual/interface calls**: Class Hierarchy Analysis (CHA) is performed. Starting from the statically declared target method vertex, all overriding implementations reachable through `method_super_edge_property` override edges are collected via BFS and added as potential callees. This is sound but may over-approximate (reachability is conservative).

```
collect_virtual_targets(base, method_graph):
    targets = {}
    queue = [base]
    while queue not empty:
        cur = queue.pop()
        targets.add(cur)
        for each override edge out of cur:
            queue.push(target of edge)
    return targets
```

### 6.3 Taint Domain

The taint domain for a method with `p` parameters is a **register dependency map**:

```
RegDeps: register_index → DepSet   (where DepSet = boost::dynamic_bitset of size p)
```

`RegDeps[r].test(i) = true` means register `r` holds data derived from parameter `i`.

The lattice join is bitwise OR. The domain is strictly monotone: bits can only be set, never cleared. This guarantees termination.

A **CallContext** is also a `p`-bit bitset: `ctx.test(i) = true` means parameter `i` is tainted when this method is called from a particular call site.

### 6.4 Intra-Method Dataflow Pass

`compute_summary_ctx(mid, mv, entry_ctx, ...)` performs a forward dataflow pass over one method under one call context.

#### Initialization

1. `reg_domain` = `ig[graph_bundle].registers_size`
2. `param_count` = `ig[graph_bundle].ins_size`
3. `IN[i]` and `OUT[i]` are vectors of `RegDeps` (one `DepSet` per register), initialized to all-zero.
4. `param_seed` is built from `entry_ctx`:

```
param_seed[reg_domain - param_count + i] = {i}   if entry_ctx.test(i)
param_seed[r]                             = {}    otherwise
```

In Dalvik, parameters occupy the *last* `ins_size` registers of the frame.

5. `DEF[i]` and `USE[i]` are pre-computed for every instruction, expanding wide types:
   - `sets_wide_register()` → add `idx` and `idx+1` to DEF
   - `reads_wide_register()` → add `idx` and `idx+1` to USE

6. A `FieldTaintMap` (unordered_map keyed by string) tracks taint accumulation for heap fields and array elements within this method invocation. Keys take the form:
   - `"R{reg_idx}:{Ltype;.name:Ftype;}"` — instance field on the object in register `reg_idx`
   - `"STATIC:{Ltype;.name:Ftype;}"` — static field
   - `"R{reg_idx}:[]"` — array element slot for array in register `reg_idx`

#### Fixed-Point Loop

```
changed = true
while changed:
    changed = false
    for each instruction i in order:
        compute new_in from predecessors' OUT sets (bitwise OR)
        if no predecessors:
            new_in = param_seed          ← crucial: seeds taint at entry
        new_out = new_in
        kill DEF[i] from new_out
        apply transfer function (see §6.5)
        if new_out != OUT[i]:
            OUT[i] = new_out
            changed = true
        if new_in != IN[i]:
            IN[i] = new_in
            changed = true
```

The *no-predecessors* branch restores the parameter seed. This is critical because Jitana inserts a synthetic vertex 0 (opcode = 0, NOP) at every method entry with `DEF = {param registers}`, `USE = {}`. Without the explicit re-seeding, the kill step at vertex 0 would wipe the parameter taint before any real instruction runs. See §10.1 for the full explanation.

### 6.5 Transfer Functions — Full Instruction Coverage

#### Arithmetic / Logical / Copy instructions

```
new_out[dest] = use_dep
   where use_dep = ⋃ new_in[r] for all r in USE[i]
```

If any used register is tainted, all defined registers inherit the union of all input taints.

#### Instance field read (`iget`, `iget-wide`, `iget-object`, etc.)

Register layout: `regs[0]` = destination, `regs[1]` = object.

```
key = "R{obj_reg}:{field_key}"
field_dep = field_taint[key]   (empty if not present)
new_out[dest] = use_dep | field_dep
```

This accounts for both the object's own taint (via `use_dep`) and any taint previously stored to the specific field of that object.

#### Instance field write (`iput`, `iput-wide`, `iput-object`, etc.)

Register layout: `regs[0]` = value, `regs[1]` = object.

```
key = "R{obj_reg}:{field_key}"
field_taint[key] |= new_in[val_reg]
// For wide writes also:
if iput-wide: field_taint[key] |= new_in[val_reg + 1]
```

`iput` has no register defs; `new_out` is unchanged.

#### Static field read (`sget`, `sget-wide`, `sget-object`, etc.)

```
key = "STATIC:{field_key}"
field_dep = field_taint[key]
new_out[dest] = use_dep | field_dep
```

#### Static field write (`sput`, `sput-wide`, `sput-object`, etc.)

```
key = "STATIC:{field_key}"
field_taint[key] |= new_in[val_reg]
if sput-wide: field_taint[key] |= new_in[val_reg + 1]
```

#### Array element read (`aget`, `aget-wide`, `aget-object`, etc.)

Register layout: `regs[0]` = destination, `regs[1]` = array reference, `regs[2]` = index.

```
arr_key = "R{arr_reg}:[]"
array_dep = field_taint[arr_key] | new_in[arr_reg]
new_out[dest] = array_dep
```

The array reference's own taint (`new_in[arr_reg]`) is included to handle arrays received as tainted parameters.  Index taint is intentionally not propagated.

#### Array element write (`aput`, `aput-wide`, `aput-object`, etc.)

Register layout: `regs[0]` = value, `regs[1]` = array reference, `regs[2]` = index.

```
val_dep = new_in[val_reg]
if aput-wide: val_dep |= new_in[val_reg + 1]
arr_key = "R{arr_reg}:[]"
field_taint[arr_key] |= val_dep
```

`aput` has no register defs.

#### `filled-new-array` / `filled-new-array/range`

Creates an array whose elements are the argument registers. The taint union of all arguments is staged into `new_pending` so the subsequent `move-result-object` marks the array reference as tainted.

```
new_pending = ⋃ new_in[arg] for all args
```

#### Invoke instructions (all variants)

This is the most complex case. It combines:

1. **Sink detection** — if the callee is a known sink and any argument is tainted, record a `SinkHit`.
2. **Source-to-sink detection** — if the callee is a known sink and any argument carries source-API-derived taint, record a `SourceHit`.
3. **Context-sensitive summary lookup** — construct the callee's `CallContext` from the current register state and call `get_or_compute_ctx(callee, ctx)`.
4. **Return-value taint propagation** — the callee's `return_dep` summary is applied through the actual argument mapping.
5. **Field-write propagation** — the callee's `field_write_deps` are translated from callee parameter indices to caller register/source indices.

```
// Build callee context
CallContext callee_ctx(args.size())
for each (pi, arg_reg) in enumerate(args):
    if new_in[arg_reg].any(): callee_ctx.set(pi)

// Lookup summary
callee_sum = get_or_compute_ctx(callee, callee_ctx)

// Return-value propagation (staged into new_pending for move-result)
for each pi where callee_sum.return_dep.test(pi):
    new_pending |= new_in[args[pi]]

// Field-write propagation
for each (callee_key, dep) in callee_sum.field_write_deps:
    translated = ⋃ new_in[args[pi]] for all pi where dep.test(pi)
    if callee_key starts with "P{k}:":
        caller_key = "R{args[k]}:{fkey}"
    elif callee_key starts with "STATIC:":
        caller_key = callee_key
    field_taint[caller_key] |= translated
```

#### `move-result` / `move-result-object` / `move-result-wide`

```
new_out[dest] = new_pending    ← the return-value taint staged by the invoke
new_src_out[dest] = src_incoming  ← source-taint from preceding source-API invoke
```

#### `return` / `return-object` / `return-wide`

```
sum.return_dep |= use_dep
```

Accumulates which parameters influence any return value.

#### Constants, unconditional branches, throws

No taint generation. DEF registers are killed by the common kill step.

### 6.6 Context-Sensitive Summary Memoization (CtxCache)

Naive per-(method, context) analysis would be exponential. `CtxCache` memoizes summaries and handles recursive cycles:

```cpp
struct CtxCache {
    unordered_map<CtxKey, MethodSummary>         summaries;   // completed
    unordered_set<CtxKey>                         in_progress; // currently on stack
    unordered_map<CtxKey, MethodSummary>         interim;     // optimistic placeholder
    vector<CtxKey>                                call_stack;
    unordered_map<CtxKey, vector<CtxKey>>        added_during;// dependents to evict
    unordered_map<string, unordered_set<string>> supertype_cache; // for sink matching
};
```

**`get_or_compute_ctx(mid, ctx)` algorithm:**

```
key = (mid, ctx)

if key in summaries:
    return summaries[key]         ← memoized hit

if key in in_progress:
    return interim[key]            ← optimistic bottom (empty summary)
                                     returned to break the recursive cycle

// First time seeing this (method, context) pair
in_progress.insert(key)
interim[key] = empty_summary()
call_stack.push(key)

summary = compute_summary_ctx(mid, ctx, ...)   ← full intra-method pass

call_stack.pop()
in_progress.remove(key)

if summary != interim[key]:
    // Our optimistic summary was too conservative; evict any callers that
    // used our interim value and re-analyse them.
    evict_dependents(key)
    interim[key] = summary
    // Caller will be re-run on next pass

summaries[key] = summary
return summary
```

**Why this is sound:** Each `DepSet` can only grow (bits are set, never cleared). Since there are at most `p` bits per set and `p` is bounded by the method's parameter count, the fixed-point is reached in a finite number of re-analyses per `(method, context)` pair.

**Context explosion mitigation:** Most app methods have `p ≤ 4` parameters, limiting the context space to at most 16 per method. Library code is excluded from seeding (§6.9), further reducing context creation.

### 6.7 Source-to-Sink Tracking

In parallel with the parameter taint domain, a separate **source-taint domain** tracks data derived from return values of well-known source APIs (e.g., `TelephonyManager.getDeviceId`, `SmsManager.sendTextMessage`).

```
SRC_OUT[i][r]: uint8_t — 1 if register r holds source-API-derived data
src_origin[r]: MethodId — which source API produced the data in register r
```

**Source marking:** When an invoke instruction calls a known source API, the following `move-result` instruction marks the destination register as source-tainted in `SRC_OUT`.

**Source-to-sink detection:** When an invoke instruction calls a known sink and any argument register carries source taint, a `SourceHit` is recorded with both the source callee and the sink callee.

**Propagation:** For all non-invoke, non-move-result instructions, if any `USE` register is source-tainted, all `DEF` registers are marked source-tainted (same conservative use→def rule as parameter taint).

### 6.8 Sink Specification and Subtype Matching

Sinks are specified as `(type_descriptor, method_name, method_descriptor)` triples. The default set is listed in §11.

**Subtype matching:** Because Android apps frequently call sink methods through subclass references (e.g., a `BufferedOutputStream` argument passed where `FileOutputStream` is declared), JITANA-DFA checks whether the actual callee's declaring class is a *subtype* of the sink's declared class:

```
is_sink(callee):
    for each sink spec s:
        if callee.name == s.name and callee.descriptor == s.descriptor:
            if callee.type == s.type: return true   ← exact match
            supertypes = supertype_cache[callee.type]
            if empty: BFS over class graph to collect all transitive supertypes
            if s.type in supertypes: return true     ← subtype match
    return false
```

Supertype sets are lazily computed and memoized in `CtxCache.supertype_cache`.

### 6.9 Library Exclusion

Bundled library code (Android Support Library, AndroidX, Google Play Services, Retrofit, OkHttp, Kotlin runtime) is shipped inside APKs as application code. If their parameters were seeded as taint sources, they would generate large numbers of false-positive sink hits because library methods call dangerous APIs internally.

The `InterprocParamConfig.param_seed_exclude_prefixes` list controls which class descriptor prefixes are excluded from parameter seeding:

```cpp
ipc_cfg.param_seed_exclude_prefixes = {
    "Landroid/support/",    // old Android Support Library
    "Landroidx/",           // AndroidX
    "Lcom/google/android/", // Google Play Services / Firebase
    "Lcom/google/gson/",
    "Lcom/squareup/",
    "Lokhttp3/",
    "Lretrofit2/",
    "Lkotlin/",
    "Lkotlinx/",
};
```

Methods whose declaring class begins with an excluded prefix are analyzed for *taint propagation* (so their summaries are correct when called from app code) but their parameters are not seeded as independent taint sources.

**Source-to-sink detection is unaffected** — it runs in the separate source-taint domain and does not depend on parameter seeding.

---

## 7. Inter-App IPC Chain Detection

When more than one APK or DEX is loaded simultaneously, JITANA-DFA can trace taint across app boundaries through Android IPC mechanisms.

### IPC Dispatch Methods Recognized

| Method | Receiver Entry Point |
|---|---|
| `sendBroadcast`, `sendOrderedBroadcast`, `sendStickyBroadcast` | `onReceive(Context, Intent)` |
| `startActivity`, `startActivityForResult` | `onCreate(Bundle)` |
| `startService`, `startForegroundService`, `bindService` | `onStartCommand(Intent,II):I`, `onBind(Intent):IBinder` |

### Chain Structure

```cpp
struct InterAppChain {
    SinkHit     sender_hit;           // IPC dispatch call in sender APK
    MethodId    receiver_entry;       // matching entry point in receiver APK
    string      receiver_apk_name;    // filename of receiver APK
    vector<SinkHit> receiver_sink_hits; // downstream dangerous sinks in receiver
};
```

### Resolution Algorithm

**Strategy 1 — Manifest-based (preferred):**  
When APKs are loaded with their `AndroidManifest.xml` files, JITANA's `compute_explicit_intent_handlers` and `compute_implicit_intent_handlers` functions resolve intent targets to specific loader IDs. Each IPC dispatch sink hit in loader `A` is connected to receiver entry points in the loaders that the manifest analysis says can handle the intent.

**Strategy 2 — Structural fallback (no manifest):**  
When no manifest data is available (e.g., bare DEX files), every IPC dispatch sink hit in loader `A` is connected to *all* receiver entry points found in any other loader. This is over-approximate but ensures no chains are missed.

```
for each sink_hit where callee is an IPC dispatch method:
    sender_loader = sink_hit.caller.type.loader_hdl.idx
    target_loaders = sender_to_target_lids[sender_loader]  ← from manifest or all others
    eps = get_entry_points(sink_hit.callee.name)           ← onReceive / onCreate / etc.
    for each target_loader in target_loaders:
        for each method in target_loader:
            if method matches one of eps:
                collect non-IPC sink hits from target_loader
                emit InterAppChain
```

Deduplication is applied so the same (sender method, receiver entry) pair is not emitted twice.

---

## 8. The `jitana-dfa` CLI Tool

### 8.1 Input Handling (DEX and APK)

`prepare_dex_sources(input_path)` normalizes the input:

- **`.dex` file**: used directly.
- **`.apk` file**: extracted to a `boost::filesystem` temporary directory via `unzip`. All `classes*.dex` files are collected, sorted lexicographically, and used together. `AndroidManifest.xml` is also extracted (silently ignored if absent) to enable manifest-based intent routing. The temp directory is cleaned up on exit via a RAII `TempDirGuard`.

### 8.2 Bootstrap Loader and Placeholder Classes

JITANA requires class vertices to exist in the class graph for types that appear in inheritance hierarchies or as sink declaring types. Framework DEX files are typically not loaded when analyzing an app in isolation.

**Bootstrap loader (ID 0):** A special class loader with no DEX files, created before any app loader. All app loaders are added as children of the bootstrap loader, so JITANA's class lookup DFS can resolve stubs.

**Placeholder class seeding (`seed_placeholder_classes`):** A fixed list of Android/Java framework types is inserted as bare `class_vertex_property` nodes into the class graph under the bootstrap loader:

```
Java core:        Object, Class, String, System, Runtime, ProcessBuilder, ClassLoader
Java I/O:         PrintStream, FileOutputStream, FileInputStream, FileWriter,
                  RandomAccessFile
Java networking:  URL, Socket, HttpURLConnection
Android telephony:TelephonyManager, SmsManager
Android UI:       WebView
Android logging:  Log
Android SQLite:   SQLiteDatabase
JNDI:             InitialContext
Android IPC:      Context, ContextWrapper, Intent, Activity, Service,
                  BroadcastReceiver, ContentProvider, ContentResolver,
                  ContentValues, Uri, Bundle, IBinder
```

Each app loader (IDs 100, 101, …) is wired as a child of the bootstrap loader via `vm.add_loader(loader, class_loader_hdl{BOOTSTRAP_LOADER_ID})`.

### 8.3 Intraprocedural Phase

When `--interproc-only` is **not** passed, the CLI iterates over every method vertex in `vm.methods()` that has a non-empty instruction graph:

```cpp
for each method vertex mv:
    if num_vertices(method.insns) == 0: continue

    T = run_taint(vm, mv)

    // Pre-filter: only print if taint exists AND reaches a use
    tainted_union = ⋃ T.TAINT_IN | ⋃ T.TAINT_OUT
    if not tainted_union.any(): continue
    has_tainted_use = check if any tainted register appears in a USE set
    if not has_tainted_use: continue

    L = run_liveness(vm, mv)
    reuse = run_variable_reuse(vm, mv, L)
    // print method header, tainted registers, liveness, reuse candidates
```

This filters the output to only methodologically interesting methods.

### 8.4 Interprocedural Phase

Always runs regardless of `--interproc-only`:

```cpp
InterprocParamConfig ipc_cfg;
ipc_cfg.param_seed_exclude_prefixes = { ... };
auto interproc = run_interproc_param_taint(vm, ipc_cfg);
auto chains = compute_ipc_chains(vm, interproc, loader_names);
```

### 8.5 Output and Reporting

**Method summaries** (interprocedural): All methods whose `return_dep` is non-empty are sorted and printed:

```
[+] Interprocedural parameter taint summaries
    100:LMyClass;.process(Ljava/lang/String;)V ReturnDependsOn = {0}
```

**Tainted sink hits:**

```
[+] Tainted sink hits
    100:LMyClass;.run(Ljava/lang/String;)V (arg1) -> Ljava/lang/Runtime;.exec @off 0x1a
```

**Source-to-sink flows:**

```
[+] Source-to-sink flows
    [in 100:LMyClass;.foo()V] Landroid/telephony/TelephonyManager;.getDeviceId
    -> Landroid/util/Log;.i (arg1) @off 0x2c
```

**Inter-app chains:**

```
[+] Inter-app IPC chains (1 found)
    100:LSenderApp;.onClick(View)V -> sendBroadcast ~~[IPC]~~ LReceiverApp;.onReceive [receiver.apk] -> 2 downstream sink(s)
```

---

## 9. DOT Graph Visualization

When `--taint-graph FILE` is passed, JITANA-DFA writes a GraphViz DOT file showing taint flow from app code to sink APIs. Two layouts are used depending on whether inter-app chains were detected.

### Node Labels

All nodes use HTML table labels rendered by GraphViz:

```
┌──────────────────────────┐
│   ClassName              │  ← colored header (class name only)
├──────────────────────────┤
│   app.apk                │  ← APK filename or "Android Framework" / "Java SDK"
├──────────────────────────┤
│   com.example.package    │  ← grey package row
├──────────────────────────┤
│   methodName(Type): Ret  │  ← Java-style method signature
└──────────────────────────┘
```

JVM descriptors (`Ljava/lang/String;`, `(I[B)V`) are translated to Java-style names (`String`, `(int, byte[]): void`) by `type_desc_to_java` and `method_desc_to_java`.

### 9.1 Two-Level Layout (Single App)

Used when no inter-app chains are found.

```
cluster_callers (blue)                cluster_sinks (red/orange)
┌──────────────────────┐             ┌────────────────────────┐
│  App methods that    │  ─────────▶ │  Dangerous sink APIs   │
│  pass tainted params │             │  (red = dangerous,     │
│  to sinks            │             │   orange = IPC)        │
└──────────────────────┘             └────────────────────────┘
```

Edge labels show tainted argument indices, types, and bytecode offsets. Multiple call sites to the same sink from the same caller are merged into one edge annotated with a count.

### 9.2 Four-Level Layout (Inter-App Chains)

Used when at least one inter-app chain is detected. Layout direction is left-to-right (`rankdir=LR`).

```
Level 1 (Blue)       Level 2 (Orange)      Level 3 (Green)       Level 4 (Red)
Sender methods    →  IPC / Inter-app    → Receiver entry      →  Dangerous sink
in originating APK   APIs (sendBroadcast,  points in target APK   APIs reached from
                     putExtra, ...)        (onReceive, onCreate)   receiver
```

Edge styles:
- **Level 1 → Level 2** (solid orange): tainted argument details + bytecode offset
- **Level 2 → Level 3** (dashed green): `IPC boundary` label — marks data crossing the app boundary
- **Level 3 → Level 4** (solid red): tainted argument details + bytecode offset

A legend subgraph is included in every graph explaining the color scheme and argument numbering convention (`arg0 = this` for virtual calls, `arg1 = first explicit parameter`, etc.).

---

## 10. Key Algorithmic Challenges and Solutions

### 10.1 The Synthetic Entry Vertex Kill Problem

**Problem:** Jitana inserts a synthetic vertex 0 at every method entry with:
- `DEF = {param_registers}` (all parameter registers)
- `USE = {}` (no uses)

The standard dataflow kill step (`new_out[r].reset()` for each `r` in `DEF[i]`) executes at this vertex *before* any real instruction. Since vertex 0 has no predecessors, `new_in` starts as all-zero. After the kill step, all parameter registers in `new_out` are also zero — the parameter taint has been erased before it was ever propagated.

**Solution:** Detect when a vertex has no control-flow predecessors (`saw_pred = false`) and unconditionally restore the parameter seed after the kill/gen steps:

```cpp
if (!saw_pred) {
    for (std::size_t r = 0; r < reg_domain; ++r) {
        new_out[r] |= param_seed[r];
    }
}
```

This is not merely an optimization — without it the entire analysis produces empty taint for all methods.

### 10.2 Wide Register Pairs

Dalvik's `long` and `double` types occupy two consecutive registers but Dalvik instructions name only the lower-numbered register in their operand encoding. JITANA exposes `sets_wide_register()` and `reads_wide_register()` flags on instruction info.

**Solution:** When building `DEF[i]` and `USE[i]`, JITANA-DFA explicitly adds `idx + 1` (if within `reg_domain`) whenever the wide flag is set:

```cpp
if (iinfo.sets_wide_register() && idx + 1 < reg_domain)
    DEF[i].push_back(idx + 1);
if (iinfo.reads_wide_register() && idx + 1 < reg_domain)
    USE[i].push_back(idx + 1);
```

For `iput-wide`, `sput-wide`, and `aput-wide`, the high-word register is explicitly OR-ed into the field taint:

```cpp
if (opcode == op_iput_wide && val_idx + 1 < new_in.size())
    ft |= new_in[val_idx + 1];
```

### 10.3 Field Taint Key Design

**Problem:** A naive implementation would taint all fields of an object whenever any field was written with tainted data, regardless of which field. This causes excessive over-approximation.

**Solution:** The `FieldTaintMap` keys combine the object register index and the fully-qualified field descriptor:

```
"R{reg}:{Ltype;.name:Ftype;}"   — object in register reg, field key
"STATIC:{Ltype;.name:Ftype;}"   — static field
"R{reg}:[]"                     — array element slot
```

Two different registers (proxy for two different objects) do not alias each other's fields. A write to `this.field1` (key `"R3:Ltype;.field1:I"`) does not taint reads of `other.field1` (key `"R5:Ltype;.field1:I"`).

The inter-method version uses `"P{k}:{fkey}"` (where `k` is a parameter index rather than a register) in `field_write_deps`. When propagating a callee's field writes to the caller, the parameter index `k` is translated to the actual argument register `args[k]`:

```
callee key "P{k}:{fkey}" → caller key "R{args[k]}:{fkey}"
```

### 10.4 Context Explosion Mitigation

**Problem:** Fully context-sensitive analysis with one analysis per `(method, context)` pair has worst-case exponential cost in the number of parameters.

**Mitigations applied:**
1. **Library exclusion** (§6.9): Library methods are not seeded as sources, so they are typically analyzed under the empty context `{}` only.
2. **Empty-context fast path**: If `callee_ctx.none()` (no argument is tainted), return a zero summary immediately without running the intra-method pass.
3. **CtxCache memoization**: Each `(method, context)` pair is analyzed at most once; subsequent lookups are O(1).
4. **Optimistic recursion breaking**: Mutually-recursive cycles are broken immediately with an empty interim summary rather than executing recursively.

---

## 11. Known Sink Set

The following sinks are recognized by default (can be overridden via `InterprocParamConfig.sinks`):

| Category | Class | Method | Significance |
|---|---|---|---|
| Shell execution | `java.lang.Runtime` | `exec` | OS command injection |
| Shell execution | `java.lang.ProcessBuilder` | `start` | OS command injection |
| File I/O | `java.io.FileOutputStream` | `<init>` | Arbitrary file write |
| File I/O | `java.io.FileWriter` | `<init>` | Arbitrary file write |
| File I/O | `java.io.RandomAccessFile` | `<init>` | Arbitrary file read/write |
| Networking | `java.net.URL` | `openConnection` | SSRF / data exfiltration |
| Networking | `java.net.Socket` | `<init>` | Outbound connection |
| Networking | `java.net.HttpURLConnection` | `setRequestProperty` | Header injection |
| Logging | `android.util.Log` | `i`, `d`, `e`, `w`, `v` | Log injection / info leak |
| WebView | `android.webkit.WebView` | `loadUrl` | JavaScript injection / XSS |
| WebView | `android.webkit.WebView` | `loadData` | Content injection |
| Telephony | `android.telephony.SmsManager` | `sendTextMessage` | SMS exfiltration |
| Database | `android.database.sqlite.SQLiteDatabase` | `execSQL` | SQL injection |
| Database | `android.database.sqlite.SQLiteDatabase` | `rawQuery` | SQL injection |
| JNDI | `javax.naming.InitialContext` | `lookup` | JNDI injection |
| IPC | `android.content.Context` | `sendBroadcast`, `startActivity`, `startService` | Intent injection |
| IPC | `android.content.ContentResolver` | `query`, `insert`, `update`, `delete` | Content injection |

Subtype matching (§6.8) means subclasses of these types are also recognized as sinks.

---

## 12. Building and Running

### Build

```bash
cd /Users/gurvinder/Desktop/build
cmake /Users/gurvinder/Desktop/jitana
make jitana-dfa
```

The binary is produced at `tools/jitana-dfa/jitana-dfa`.

### Usage

```
jitana-dfa [OPTIONS] <file.dex|app.apk> [<file2.dex|app2.apk> ...]

Options:
  --taint-graph FILE   Write DOT taint flow graph to FILE
  --interproc-only     Skip per-method intraprocedural output; run
                       interprocedural analysis only
  --quiet, -q          Suppress verbose console output (graph still
                       written if --taint-graph is given)
```

Multiple input files can be specified; each is loaded into its own classloader (IDs 100, 101, …) enabling inter-app IPC chain detection.

### Example Invocations

```bash
# Single DEX, full output
./jitana-dfa taint_test.dex

# Single APK, interprocedural only, write graph
./jitana-dfa --interproc-only --taint-graph taint.dot MyApp.apk

# Two APKs for inter-app analysis
./jitana-dfa --taint-graph ipc.dot SenderApp.apk ReceiverApp.apk

# Render graph
dot -Tpng taint.dot -o taint.png
```

### Interpreting the Output

| Output section | What it means |
|---|---|
| `[+] Interprocedural parameter taint summaries` | Methods whose return value can be influenced by their parameters |
| `[+] Tainted sink hits` | Call sites where a parameter-derived value reaches a dangerous API |
| `[+] Source-to-sink flows` | Flows from a known source API return value to a dangerous sink |
| `[+] Inter-app IPC chains` | Tainted parameter → IPC dispatch → receiver entry → downstream sink |

In the **taint graph**:
- A **blue** node is an app method that passes tainted data to a sink.
- A **red** node is a dangerous sink API.
- An **orange** node is an IPC/inter-app API (Intent dispatch, ContentResolver).
- A **green** node is a receiver entry point in a target APK.
- A **dashed arrow** marks the IPC boundary where data crosses an app boundary.
- Edge labels show which argument (0-based, where `arg0 = this` for virtual calls) is tainted and at which bytecode offset the call occurs.
