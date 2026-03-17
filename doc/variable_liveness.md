# Liveness Analysis Overview

This note summarizes the intraprocedural liveness analysis added to Jitana and
the CLI utility that exercises it (`tools/jitana-dfa`).

## Files and Entry Points

| File | Purpose |
| --- | --- |
| `include/jitana/analysis/variable_liveness.hpp` | Public API that exposes `analysis::dfa::LivenessResult` and `run_liveness(virtual_machine&, method_vertex_descriptor)` |
| `lib/jitana/analysis/variable_liveness.cpp` | Implementation of the data-flow engine |
| `tools/jitana-dfa/main.cpp` | Standalone binary that loads a DEX/APK, runs liveness for every method with code, and prints `LIVE_IN` / `LIVE_OUT` |

## LivenessResult surface

```cpp
struct LivenessResult {
    std::vector<insn_vertex_descriptor> order;
    std::vector<boost::dynamic_bitset<>> LIVE_IN;
    std::vector<boost::dynamic_bitset<>> LIVE_OUT;
    std::size_t reg_domain{0};
};
```

* `order` captures the walk order over the method’s instruction graph.
* `LIVE_IN[i]` / `LIVE_OUT[i]` correspond to `order[i]`.
* `reg_domain` (bitset width) equals the method’s `registers_size` from the
  DEX code item.

## Algorithm (lib/jitana/analysis/variable_liveness.cpp)

1. **Instruction Order**  
   `build_order` copies the instruction graph’s vertex descriptors into a
   vector. No special sorting is required because we merely need a consistent
   iteration order.

2. **Initialization**  
   * `reg_domain` is set to `ig[boost::graph_bundle].registers_size`.
   * `LIVE_IN`, `LIVE_OUT`, `USE`, `DEF` are vectors of bitsets sized to the
     register domain.
   * A dense `index_of` array maps each vertex descriptor back to its index in
     `order` so successor lookups avoid `std::find`.

3. **USE/DEF computation**  
   For every instruction:
   ```cpp
   add_regs(DEF[i], defs(insn));
   add_regs(USE[i], uses(insn));
   ```
   * `defs` / `uses` come from the existing instruction helpers in
     `include/jitana/vm_core/insn.hpp`.
   * `add_regs` ignores pseudo registers (`result`, `exception`) and any
     negative/invalid indices, ensuring we only touch real virtual registers.

4. **Fixed-point iteration**  
   Classic backward equations:
   ```cpp
   LIVE_OUT[i] = ⋃ LIVE_IN[succ(i)]
   LIVE_IN[i]  = USE[i] ∪ (LIVE_OUT[i] \ DEF[i])
   ```
   We iterate in reverse order until no bitset changes. Bitsets are
   `boost::dynamic_bitset` to keep memory compact and provide fast bit ops.

5. **Result**  
   Once stable, `R.order`, `R.LIVE_IN`, `R.LIVE_OUT`, and `R.reg_domain` are
   returned to the caller unchanged for inspection or further processing.

## CLI (tools/jitana-dfa/main.cpp)

High-level flow:

1. **Input normalization**  
   * If the path ends with `.dex`, we use it directly.
   * If the path ends with `.apk`, we extract all `classes*.dex` files to a
     temporary directory (using Boost Filesystem utilities) and feed their paths
     into the loader.
   * A small list of placeholder classes (e.g. `java/lang/Object`) is seeded
     so standalone DEXes that reference framework types still load.

2. **Loader wiring**  
   `wire_loader` adds a dedicated class loader (ID `100`) with the prepared
   DEX file list, calls `vm.load_all_classes`, and logs any classes that could
   not be loaded (e.g., framework-dependent APKs).

3. **Per-method analysis**  
   For each vertex in `vm.methods()` with a non-empty instruction graph:
   ```cpp
   auto L = analysis::dfa::run_liveness(vm, mv);
   ```
   The CLI prints the JVM handle (`package/class.method(sig)`), instruction
   count, register domain size, and all `LIVE_IN`/`LIVE_OUT` sets.

4. **Output sample**
   ```
   [+] Method #2: 100:LSimpleTest;.main([Ljava/lang/String;)V
       Instructions analyzed: 15
       Register domain size : 4
       [insn#7] LIVE_IN: v0 v1 v3  | LIVE_OUT: v0 v1 v2 v3
   ```

## Notes

* Analysis is **intraprocedural** (per method). To cover all methods, we run
  the solver once per method vertex.
* No heap ownership helpers (`new`/`delete`) are used; temporary directories are
  managed with RAII (`TempDirGuard`).
* Boost Filesystem is used for temp directories and APK extraction; link flags
  were updated (`find_package` now requests `filesystem`).
* The implementation follows the “textbook” liveness algorithm; there are no
  custom heuristics beyond the placeholder seeding for missing framework types.
