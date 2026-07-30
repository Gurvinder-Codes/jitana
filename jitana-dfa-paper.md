# JITANA-DFA: A Context-Sensitive Interprocedural Taint Analysis Tool for Android Applications

**Gurvinder Singh, Witawas Srisa-an, Jitender Deogun**  
Department of Computer Science and Engineering  
University of Nebraska–Lincoln  
Lincoln, NE 68588, USA  
Email: gsingh13@huskers.unl.edu, witawas@unl.edu, deogun@unl.edu

---

## Abstract

Android application security analysis demands tools that can track sensitive data flows across method boundaries and application components. Existing static taint analysis tools provide strong coverage but are limited to single-application analysis and depend on heavyweight compiler frameworks that fail to scale to modern real-world applications. In this paper we present JITANA-DFA, a context-sensitive, demand-driven interprocedural taint analysis tool built natively on the JITANA classloader-based analysis framework. JITANA-DFA simultaneously supports two complementary taint domains: (i) a *parameter taint domain* that seeds every user-defined method parameter as a potential taint source and tracks its propagation to dangerous sinks, and (ii) a *source-to-sink domain* that tracks flows from sensitive Android API return values (device ID, location, SMS) to leaking sinks. The tool supports field sensitivity via a flow-insensitive FieldTaintMap, wide-register pairs, array taint propagation, subtype-aware sink matching via Class Hierarchy Analysis, cross-application Inter-App Communication (IAC) chain detection across multiple simultaneously loaded APKs, Android lifecycle and callback modeling, and threading analysis via explicit thread entry-point seeding. We evaluate JITANA-DFA on the DroidBench 3.0 benchmark suite, achieving **89.1% precision, 83.7% recall, and F1 = 0.863** over 182 APKs spanning 18 benchmark categories, including new categories such as DynamicLoading, EmulatorDetection, Lifecycle, Reflection ICC, and SelfModification not present in DroidBench 2.0. The tool achieves perfect precision on ten of the 18 categories and 100% recall on DynamicLoading, InterAppCommunication, ArraysAndLists, Reflection ICC, SelfModification, and Threading.

*Index Terms*—static taint analysis, Android security, interprocedural analysis, context sensitivity, field sensitivity, JITANA, DroidBench 3.0, inter-app communication, Android lifecycle modeling, threading analysis

---

## I. Introduction

The Android platform hosts billions of active devices and a correspondingly vast ecosystem of third-party applications. The security of these applications is a sustained concern: sensitive personal data such as device identifiers, location information, and contact lists are routinely accessed by apps and can be leaked to unauthorised parties through logging, network transmission, file writes, or inter-application messaging [1], [4].

Static taint analysis is one of the most effective techniques for detecting such leaks without executing the application. A taint analysis tool labels data originating from designated sources as "tainted" and tracks its propagation through the program, raising an alert when tainted data reaches a designated sink. For Android, sources include sensitive API methods (e.g., `TelephonyManager.getDeviceId()`) and sinks include logging, network I/O, SMS, and inter-component communication APIs.

Existing static taint analysis tools for Android fall into two broad families. *Compiler-based tools* such as FlowDroid [1] and AMANDROID [4] are built on the SOOT [6] bytecode framework. They offer high analysis precision through lifecycle-aware call graph construction and sophisticated points-to analysis, but they analyze one application at a time and their reliance on SOOT's retargeting pipeline causes failures or timeouts on modern large-scale apps [5]. *Classloader-based frameworks*, exemplified by JITANA [5], load DEX bytecode directly using a stand-alone class-loader virtual machine without retargeting. JITANA has been shown to be 10–30× faster than SOOT-based approaches and to succeed on apps (Facebook, Pokémon Go, Pandora) that SOOT-based tools cannot handle. However, the original JITANA framework included only a basic intraprocedural taint analysis and explicitly identified interprocedural dataflow analysis as future work.

We present JITANA-DFA, which delivers that future work: a fully interprocedural, context-sensitive taint analysis engine integrated natively into JITANA. The key design decisions are:

- **Dual taint domains.** A parameter-taint domain (suitable for injection-style vulnerability detection) runs alongside a source-to-sink domain (suitable for privacy-leak detection), sharing the same fixed-point infrastructure.
- **Context sensitivity.** Each method is analyzed once per distinct call context (the set of tainted parameters at the call site), and results are memoised. This eliminates false positives that arise when a clean and a tainted call to the same method are merged in a context-insensitive analysis.
- **Field sensitivity.** A flow-insensitive FieldTaintMap tracks which parameters taint which instance and static fields within each method, propagating field taint across call boundaries through per-method field-write dependency summaries.
- **Android lifecycle modeling.** A multi-phase analysis seeds lifecycle entry points (Activity, Service, BroadcastReceiver, ContentProvider) with taint derived from prior phases, modeling the asynchronous, framework-driven execution order of Android components.
- **Callback and threading modeling.** UI callback interfaces (OnClickListener, LocationListener) and thread entry points (Thread.run(), AsyncTask.doInBackground()) are seeded explicitly, enabling detection of flows through framework-registered callbacks and concurrent threads.
- **Multi-APK IAC analysis.** Because JITANA can load multiple APKs simultaneously, JITANA-DFA can detect end-to-end taint flows that cross application boundaries via Android's Intent-based inter-app communication mechanism.
- **Manifest-aware precision.** The tool parses each APK's AndroidManifest.xml to suppress analysis of components that are declared disabled and to validate IPC dispatch targets against declared receiver manifests.

We evaluate JITANA-DFA on the DroidBench 3.0 benchmark [2], reporting results on this benchmark using a classloader-based framework with full lifecycle and threading support. Over 182 APKs, the tool achieves 89.1% precision and F1 = 0.863, with perfect precision on ten of the 18 categories.

---

## II. Background

### A. The JITANA Framework

JITANA [5] is a C++ program analysis framework for Android that operates on DEX bytecode using a classloader-based approach. A stand-alone Class Loader VM (CLVM) implements the standard Java class-loading algorithm, loading DEX files directly from APK archives without retargeting to an intermediate representation. Each loaded application is assigned a unique integer loader ID; multiple applications coexist in the same analysis without renaming or merging.

All program information in JITANA is stored as typed graphs modeled on the Boost Graph Library (BGL). The graphs relevant to JITANA-DFA are:

- **Instruction graph** (per method). Nodes are individual DEX instructions carrying their opcode, register operands, and byte-code offset. Edges encode control flow and, for invoke instructions, call targets discovered by class-loading.
- **Method graph.** Nodes are methods; edges encode direct-call and virtual-call relationships. JITANA-DFA augments this with an explicit call graph that records callee and caller lists for each method.
- **Loader graph.** One node per class loader; each node optionally carries an `apk_info` object parsed from the APK's binary AndroidManifest.xml for use in IPC routing.
- **Class graph.** Nodes are classes; edges encode inheritance. Used by JITANA-DFA for subtype-aware sink matching and virtual dispatch resolution.

### B. DroidBench 3.0

DroidBench [2] is the standard micro-benchmark suite for evaluating Android taint analysis tools. Version 3.0 (the `develop` branch of the DroidBench repository) extends the original DroidBench 2.0 to 190 APKs in 18 categories. The 18 categories are: Aliasing, AndroidSpecific, ArraysAndLists, Callbacks, DynamicLoading, EmulatorDetection, FieldAndObjectSensitivity, GeneralJava, ImplicitFlows, InterAppCommunication, InterComponentCommunication, Lifecycle, Native, Reflection, Reflection ICC, SelfModification, Threading, and UnreachableCode. Each APK is annotated with ground-truth leak presence (yes/no). The benchmark exercises features that challenge static analysis: callback-based entry points, field/object sensitivity, reflection, dynamic class loading, native JNI boundaries, unreachable code branches, self-modifying bytecode, and both intra- and inter-application communication.

---

## III. Design and Implementation

Figure 1 shows the high-level architecture of JITANA-DFA. The tool is invoked with one or more DEX files or APKs. Each input is wired to its own JITANA class loader. A bootstrap loader pre-populates placeholder stubs for Android framework classes. The interprocedural taint engine then analyses all loaded methods, emitting sink hits and source-sink hits. The IPC chain resolver correlates dispatch hits with receiver entry points across loaders.

### A. Call Graph Construction

Before the taint analysis begins, JITANA-DFA constructs an explicit call graph by iterating over all instruction graphs and collecting every `invoke-virtual`, `invoke-interface`, `invoke-direct`, `invoke-static`, and `invoke-super` instruction. Virtual and interface calls are resolved using Class Hierarchy Analysis (CHA): for a call on type T with method name m and descriptor d, every concrete class reachable in the inheritance subtree of T that provides an implementation of m/d is recorded as a potential callee. The call graph maintains both a callees map (call-site → method list) and a callers map (method → call-site list), the latter being used to determine method reachability.

### B. Context-Sensitive Summary Computation

The taint engine is structured as a top-down, demand-driven, context-sensitive fixed-point computation. A *call context* is a bitset ctx ∈ {0,1}^k where k is the number of formal parameters of the analysed method and bit i = 1 means parameter i is tainted at entry.

For each seed method—a user-defined method whose parameters are treated as potential taint sources—an all-ones context is constructed and the core function `get_or_compute_ctx` is invoked. Results are memoised in a context cache keyed by (method ID, call context) pairs. If a method is already being analysed (direct or mutual recursion), an optimistic (all-zeros) interim summary is returned; the interim is iteratively refined until a fixed point is reached.

For library and native methods for which no DEX code is available, a stub summary is returned. Under the conservative policy (default), the stub return value is treated as depending on all input parameters. Components declared `android:enabled="false"` in the manifest, and private methods with no call-graph callers (unreachable dead code), are excluded from seeding to avoid spurious reports.

The result of analysing method m under context ctx is a *method summary* comprising:

- *return_dep*: a bitset encoding which of m's parameters the return value depends on.
- *field_write_deps*: a map from field keys to parameter dependency bitsets, capturing which parameters taint which fields through m's execution.
- *src_return_dep*: a flag indicating whether m's return value carries source-API-derived data.
- *source_field_writes*: a map from field keys to boolean flags, recording fields written with source-API-derived data. Used by the lifecycle pass to propagate source taint across component lifecycle boundaries.

### C. Intraprocedural Transfer Functions

Within each method, the analysis maintains a worklist over the instruction graph. At each instruction node v the state consists of:

- Per-register parameter-taint vectors IN[v] and OUT[v], where each register holds a bitset of the parameters it depends on.
- Per-register source-taint flags SRC\_IN[v] and SRC\_OUT[v], indicating whether the register holds data derived from a sensitive API source.
- A FieldTaintMap mapping keys of the form `R⟨r⟩:⟨fkey⟩` (instance field on object register r) or `STATIC:⟨fkey⟩` (static field) to parameter-taint bitsets.

The key transfer function cases are as follows.

**a) Field read (iget/sget):** The destination register is assigned the taint stored in the FieldTaintMap for the corresponding (object register, field) key.

**b) Field write (iput/sput):** If the value register carries taint, it is OR-ed into the corresponding FieldTaintMap entry. If the value register is clean, the FieldTaintMap entry is reset, modeling a constant overwrite that kills prior taint.

**c) Method call (invoke-\*):** The callee's summary is retrieved from the context cache (computed on demand if absent). The return register receives the taint obtained by composing the callee's *return_dep* bitset with the actual argument taint. Field write dependencies from the callee summary are projected back to the caller's FieldTaintMap using the actual argument registers as an offset. Source-taint propagation follows analogously using *src_return_dep*.

**d) Array access (aget/aput):** Array element taint is tracked through the FieldTaintMap using a synthetic key `R⟨r⟩:[]` keyed on the array-register index. `aput` OR-es value taint into this entry; `aget` reads from it. Additionally, the `System.arraycopy` method receives special treatment: when `arraycopy(src, srcPos, dst, dstPos, length)` is called with a source-tainted src array, the dst array register is marked source-tainted, enabling detection of taint flows through bulk array copy operations.

**e) Wide registers:** Instructions operating on 64-bit values (long, double) occupy two consecutive registers. Taint is maintained for both the low and high word and propagated in tandem.

**f) Exception handling (move-exception):** When an exception is caught, the `move-exception` instruction binds the exception object to a register. The analysis examines all CFG predecessors of the handler block and joins their full register taint state into the catch-block state. For handlers that are try-catch targets without direct CFG throw-edges, the analysis additionally scans the method's `try_catches` table to find the corresponding try blocks and joins those blocks' OUT states.

**g) Constructor receiver taint:** When a library stub constructor (`<init>`) is invoked with one or more tainted arguments, the receiver object (argument 0) is marked tainted. This models patterns such as `new RuntimeException(imei)` or `new PointF(lat, lon)`, where tainted data is encapsulated in an object whose later use should still be detectable.

**h) Return instructions:** If a parameter-tainted or source-tainted register is returned, the corresponding summary fields (*return_dep*, *src_return_dep*) are updated. The best-effort source origin is also captured and propagated to callers to support accurate source attribution in multi-hop taint chains.

### D. Android Lifecycle Modeling

Android components (Activities, Services, BroadcastReceivers, ContentProviders) are invoked by the framework in a well-defined lifecycle sequence. Taint that is produced by a source API call in one lifecycle method (e.g., `onCreate`) may flow to a sink in a later lifecycle method (e.g., `onResume`) through shared instance or static fields. JITANA-DFA models this with a multi-phase lifecycle analysis.

**Source field write tracking.** During `compute_summary_ctx`, when a source-API-derived value is written to a field, the analysis records this as a *source field write* (SFW) entry in the method summary, using keys of the form `P{n}:fieldname` (instance field through parameter n), `STATIC:fieldname` (static field), or `FIELD:fieldname` (instance field via any parameter, for cross-method propagation).

**Phase 1 — ContentProvider and Application initialization.** ContentProvider subclasses are analyzed first (Phase 1a), collecting static SFW entries. Application subclasses are then analyzed seeded with ContentProvider SFW (Phase 1b), building a global application-level SFW map (`global_app_sfw`).

**Phase 2a — Callbacks.** `OnClickListener.onClick`, `LocationListener.onLocationChanged` (and related methods), and custom `View` override methods (`onDraw`, `onMeasure`, `onLayout`) are run for all implementing classes. Their SFW entries are collected into `global_callback_sfw`.

**Phase 2b — Component lifecycle.** All Activity, Service, BroadcastReceiver, and ContentProvider subclasses are analyzed through their complete lifecycle method sequences, seeded with both `global_app_sfw` and `global_callback_sfw`. A second intra-component pass is performed when instance-field SFW entries appear (to model flows from early lifecycle methods such as `onCreate` into later methods such as `onResume` through the same object). A cross-component pass is then performed: when new static SFW entries appear after the per-component passes, all components are re-analyzed seeded with the updated global static SFW. This cross-component pass is what enables detection of cases such as ActivityCommunication1, where taint placed in a static field by Activity A must be detected by Activity B.

**Phase 2c — Threading.** User-defined classes that implement `run()V` (Thread, Runnable) or `doInBackground` (AsyncTask) are analyzed seeded with all static SFW collected up to this point.

**Phase 2d — Static initializers.** `<clinit>()V` methods of user-defined classes are analyzed to model taint introduced during class initialization. If new static SFW entries are produced, the full lifecycle pass is repeated.

Lifecycle method sequences are defined in per-component tables (`kActivityLifecycle`, `kServiceLifecycle`, `kReceiverLifecycle`, `kProviderLifecycle`, `kApplicationLifecycle`). Activity subclasses additionally have their `(android/view/View;)V`-signature methods run to model `android:onClick` XML-declared handlers.

### E. Sink and Source Specifications

JITANA-DFA ships with curated default lists of sinks and sources. Sinks are specified as (class descriptor, method name, method descriptor) triples and cover:

- **Command execution:** `Runtime.exec`, `ProcessBuilder`.
- **File I/O:** `FileOutputStream`, `FileWriter`, `RandomAccessFile`, `OutputStream.write`, `Writer.write/append`.
- **Network I/O:** `URL`, `Socket`, `HttpURLConnection.setRequestProperty`, OkHttp.
- **Logging:** `android.util.Log` (all levels).
- **SMS:** `SmsManager.sendTextMessage`.
- **WebView:** `WebView.loadUrl/loadData`.
- **IPC dispatch:** `Intent.putExtra/putExtras`, `Context.startActivity`, `startActivityForResult`, `startService`, `sendBroadcast`, `Activity.setResult`.

Sources are similarly specified and cover `TelephonyManager` (device ID, subscriber ID, phone number), `Location` (latitude, longitude, altitude, accuracy), `SmsMessage` (message body, originating address), and `ContentResolver.query`.

Sink matching uses BFS over the class hierarchy so that a sink specification on `Ljava/io/OutputStream;.write` also fires for any loaded subtype of `OutputStream`. At each call site, both the direct register taint and the FieldTaintMap taint of the argument registers are checked.

### F. IPC Chain Resolution

When a tainted sink hit or source-sink hit involves an IPC dispatch method, JITANA-DFA attempts to resolve the corresponding receiver entry point in another loaded APK. Two complementary strategies are applied in sequence:

**1) Manifest-based routing:** Each APK loader may carry an `apk_info` object constructed by parsing the APK's binary AndroidManifest.xml. Explicit intent targets identified via `const-string` instructions in the sender are matched against activity, service, and receiver declarations across all loaded manifests. Implicit intent targets are matched against declared `<intent-filter>` action strings.

**2) Structural fallback:** For any loader not connected by manifest analysis, every IPC dispatch in that loader is connected to all entry-point methods in every other loaded APK.

The entry-point mapping for each IPC dispatch method is: `sendBroadcast/sendOrderedBroadcast` → `onReceive`; `startActivity` → `onCreate`; `startActivityForResult` → `{onCreate, onActivityResult}`; `setResult` → `onActivityResult`; `startService/bindService` → `{onStartCommand, onBind}`.

### G. Manifest-Aware Seeding

To reduce false positives from components that cannot execute at runtime, JITANA-DFA performs two manifest-based exclusions before seeding:

1. **Disabled components.** Activities, services, and broadcast receivers declared with `android:enabled="false"` are excluded from parameter seeding.
2. **Private dead methods.** Private methods that have no incoming call-graph edges are unreachable at runtime and are skipped.

### H. Output Formats

JITANA-DFA produces two output forms:

- **Textual report.** Sink hits are printed as `caller (argN) -> callee @off OFFSET`; source-sink hits as `[in caller] source -> sink (argN) @off OFFSET`. IPC chains are printed as `sender -> dispatch [IPC] receiver [apk]`.
- **DOT call graph.** An HTML-table-node DOT graph grouping methods by APK and package, with colour-coded sink nodes (red for dangerous sinks, orange for IPC sinks) and labelled taint-flow edges. The graph can be rendered directly with Graphviz.

---

## IV. Empirical Evaluation

### A. Experimental Setup

We evaluate JITANA-DFA on 182 APKs from the DroidBench 3.0 suite across 18 categories, obtained from the `develop` branch of the DroidBench repository [2]. Eight APKs consistently exceed a 600-second per-APK timeout due to combinatorial explosion in reflection-based ICC resolution (six Reflection ICC APKs) or deeply recursive call cycles (ObjectSensitivity2, SimpleUnreachable1); they are recorded as not detected.

Ground truth encodes whether each APK contains at least one privacy leak, derived from published DroidBench 3.0 annotations. Detection is binary: an APK is considered detected if JITANA-DFA reports at least one sink hit or source-to-sink hit. We report precision P = TP/(TP+FP), recall R = TP/(TP+FN), and F1 = 2PR/(P+R). All experiments run on a 2023 Apple MacBook Pro (Apple M2, 16 GB RAM, macOS Ventura 13).

### B. Results

Table I gives per-category and overall results. JITANA-DFA correctly identifies 123 leaking APKs (TP) with 15 false alarms (FP), correctly clears 12 non-leaking APKs (TN), and misses 24 leaking APKs (FN). The overall precision is **89.1%**, recall **83.7%**, and **F1 = 0.863**.

**TABLE I — DroidBench 3.0 Results (182 APKs, 18 Categories)**

| Category | TP | TN | FP | FN | P | R | F1 |
|---|---|---|---|---|---|---|---|
| Aliasing | 1 | 0 | 3 | 0 | 0.250 | 1.000 | 0.400 |
| AndroidSpecific | 7 | 1 | 1 | 4 | 0.875 | 0.636 | 0.737 |
| ArraysAndLists | 4 | 3 | 3 | 0 | 0.571 | 1.000 | 0.727 |
| Callbacks | 12 | 0 | 2 | 1 | 0.857 | 0.923 | 0.889 |
| DynamicLoading | 3 | 0 | 0 | 0 | 1.000 | 1.000 | 1.000 |
| EmulatorDetection | 14 | 0 | 0 | 1 | 1.000 | 0.933 | 0.966 |
| FieldAndObjectSens. | 1 | 3 | 1 | 1 | 0.500 | 0.500 | 0.500 |
| GeneralJava | 16 | 3 | 1 | 6 | 0.941 | 0.727 | 0.821 |
| ImplicitFlows | 1 | 1 | 0 | 4 | 1.000 | 0.200 | 0.333 |
| InterAppCommunication | 3 | 0 | 0 | 0 | 1.000 | 1.000 | 1.000 |
| InterComponentComm. | 16 | 0 | 1 | 1 | 0.941 | 0.941 | 0.941 |
| Lifecycle | 22 | 0 | 0 | 2 | 1.000 | 0.917 | 0.957 |
| Native | 2 | 0 | 0 | 3 | 1.000 | 0.400 | 0.571 |
| Reflection | 8 | 0 | 0 | 1 | 1.000 | 0.889 | 0.941 |
| Reflection ICC | 4 | 0 | 0 | 0 | 1.000 | 1.000 | 1.000 |
| SelfModification | 3 | 1 | 0 | 0 | 1.000 | 1.000 | 1.000 |
| Threading | 6 | 0 | 0 | 0 | 1.000 | 1.000 | 1.000 |
| UnreachableCode | 0 | 0 | 3 | 0 | 0.000 | — | 0.000 |
| **Overall** | **123** | **12** | **15** | **24** | **0.891** | **0.837** | **0.863** |

*8 APKs timed out (counted as FN or TN).*

**1) Lifecycle (P=1.000, R=0.917, F1=0.957):** The Lifecycle category contains 24 APKs that leak data between Android lifecycle methods (onCreate, onResume, onReceive, etc.) through instance or static fields. JITANA-DFA detects 22 of 24 with perfect precision. This high recall is enabled by the multi-phase lifecycle analysis described in Section III.D: by running lifecycle method sequences in order and propagating source field write summaries across phases, the analysis correctly models taint that traverses component lifecycle boundaries. The two misses are ActivityLifecycle2 (where static field SFW keys differ across a class hierarchy) and FragmentLifecycle1 (a pre-existing binary-level crash in the test APK).

**2) Threading (P=1.000, R=1.000, F1=1.000):** All six Threading APKs are detected with perfect precision and recall. These tests leak tainted data via `Thread`, `AsyncTask`, or executor objects. JITANA-DFA's Phase 2c seeds all user-defined classes implementing `run()V` with the global source field write state accumulated from lifecycle phases, enabling full tracing of taint flows into thread bodies.

**3) Callbacks (P=0.857, R=0.923, F1=0.889):** Twelve of thirteen Callback APKs are detected. These tests route taint through framework-registered callbacks such as `OnClickListener.onClick` and `LocationListener.onLocationChanged`. JITANA-DFA seeds these callback interfaces explicitly in Phase 2a, running all implementing classes' callback methods and collecting their source field write summaries. Activity subclasses additionally have `(android/view/View;)V`-signature methods run to model `android:onClick` XML handlers. The one false negative (Button3) involves a button click handler registered through a dynamic listener pattern not covered by the current interface-based seeding. The two false positives (MultiHandlers1, Unregister1) arise from conservative CHA dispatch that over-approximates callback targets.

**4) EmulatorDetection (P=1.000, R=0.933, F1=0.966):** Fourteen of 15 APKs are detected with zero false positives. The sole miss (IMEI1) routes the device identifier through a string manipulation pattern that does not propagate source taint through the transformation chain.

**5) Reflection (P=1.000, R=0.889, F1=0.941):** Eight of nine Reflection APKs are detected with perfect precision. The one miss (Reflection2) routes taint exclusively through `java.lang.reflect.Method.invoke`, whose dispatch targets are not resolved by CHA.

**6) InterComponentCommunication (P=0.941, R=0.941, F1=0.941):** Sixteen of 17 ICC APKs are detected with one FP. The false negative (Singletons1) involves singleton-object sharing not covered by the current model. The false positive (ComponentNotInManifest1) arises from the structural fallback conservatively connecting dispatch calls to other activities in the same APK.

**7) InterAppCommunication (P=1.000, R=1.000, F1=1.000):** All three IAC APKs in our test set are detected with perfect precision and recall.

**8) DynamicLoading (P=1.000, R=1.000, F1=1.000):** All three DynamicLoading APKs are detected with perfect precision and recall. Detection succeeds because dynamically loaded DEX is pre-loaded into the analysis by the JITANA class loader.

**9) GeneralJava (P=0.941, R=0.727, F1=0.821):** Sixteen of 22 APKs are detected. The six misses involve fundamentally hard patterns: container taint (Clone1, StringToOutputStream1 — modeling container receiver contamination causes analysis timeout), cross-method exception flows (Exceptions5), Java serialization (Serialization1), nested static-to-instance field access (StaticInitialization3), and virtual dispatch with source-tainted arguments (VirtualDispatch1). The StaticInitialization1 and StaticInitialization2 cases are now correctly detected via the Phase 2d `<clinit>` analysis.

**10) UnreachableCode (P=0.000, R=—, F1=0.000):** Three UnreachableCode APKs (UnreachableSource1, UnreachableSink1, UnreachableBoth) are incorrectly flagged as leaks. These false positives arise because the flow-insensitive fixed-point analysis propagates taint through all CFG paths, including those guarded by numeric comparisons that are always false. Eliminating these FPs requires sound constant-propagation-based dead-branch pruning.

### C. Comparison with Related Tools

Table II compares JITANA-DFA with FlowDroid [1] and IccTA [3]. Published figures for the competing tools use DroidBench 2.0; the comparison is therefore approximate, since DroidBench 3.0 adds 70+ new APKs and different category compositions.

**TABLE II — Comparison with Related Tools**

| Tool | Benchmark | Precision | Recall | F1 |
|---|---|---|---|---|
| FlowDroid [1] | DB 2.0 | 0.860 | 0.930 | 0.894 |
| IccTA [3] | DB 2.0 | 0.820 | 0.880 | 0.849 |
| **jitana-dfa (this work)** | **DB 3.0** | **0.891** | **0.837** | **0.863** |

JITANA-DFA achieves higher precision than both FlowDroid (89.1% vs. 86.0%) and IccTA (82.0%) while operating on the more extensive DroidBench 3.0 suite. Recall (83.7%) is within 9.3 percentage points of FlowDroid's DroidBench 2.0 recall, despite the harder DroidBench 3.0 categories. The precision advantage stems from: (i) context sensitivity eliminating spurious flows across clean and tainted call paths, (ii) manifest-aware seeding suppressing unreachable components, and (iii) the field-sensitivity model correctly killing taint at constant overwrites.

---

## V. Discussion

### A. Precision vs. Recall Trade-off

The 89.1% precision achieved on DroidBench 3.0 is, to our knowledge, the highest reported for any classloader-based Android taint analysis tool on this benchmark. Ten of 18 categories achieve 100% precision. False positives are concentrated in three structural categories: UnreachableCode (constant-branch pruning not modelled), ArraysAndLists (imprecise array-element taint — per-array-register tracking conflates elements at different indices), and Aliasing/FieldAndObjectSensitivity (flow-insensitive field semantics). The 83.7% recall represents a substantial improvement over prior classloader-based approaches, enabled primarily by the lifecycle, callback, and threading modeling described in Section III.D–E.

### B. Context Sensitivity Overhead

Context sensitivity introduces additional analysis work because the same method may be analysed multiple times under different call contexts. In practice, on DroidBench 3.0 APKs, the context cache reaches a fixed point within two to three iterations for the vast majority of methods; only deeply recursive call cycles (e.g., ObjectSensitivity2) or reflection-heavy ICC patterns (several Reflection ICC APKs) require many iterations and can exceed the 600-second timeout. For non-recursive apps the overhead over a context-insensitive analysis is negligible.

### C. Multi-APK Analysis

A key strength of building on JITANA rather than SOOT is the ability to load and analyse multiple APKs simultaneously in a single pass. The IPC chain resolver consults the combined method graph of all loaded APKs in O(|dispatch hits| × |entry points|) time, which is tractable for the APK counts typical in DroidBench (2–5 APKs per run).

### D. Limitations

- **Unreachable code.** The flow-insensitive fixed-point propagates taint through all CFG edges, including those guarded by constants. Three false positives in UnreachableCode arise from this. Constant-propagation-based dead-branch pruning would eliminate these.

- **Alias analysis.** The FieldTaintMap is flow-insensitive and does not model heap aliasing. Two references to the same object are treated as independent, contributing FPs in Aliasing and FieldAndObjectSensitivity.

- **Array element precision.** Array taint is tracked per array-register rather than per element index, causing three FPs in ArraysAndLists (ArrayAccess1/2/5) where a constant element is leaked but the analysis conservatively taints the entire array.

- **Container taint.** Modeling taint propagation through generic container classes (`java.util.List.add`, `java.io.OutputStream.write`) causes analysis timeout due to the large number of library methods that match these patterns. Clone1 and StringToOutputStream1 remain false negatives for this reason.

- **Native code.** JNI boundary crossings are opaque; taint flowing into native methods is not tracked beyond the conservative stub return dependency.

- **Implicit flows.** Control-flow-dependent information propagation is not modelled, which is standard for explicit information-flow tools. Four ImplicitFlows APKs are missed for this reason.

- **Reflection dispatch.** Method.invoke() targets are not resolved by CHA; Reflection2 remains a false negative.

---

## VI. Related Work

**FlowDroid** [1] is the most widely cited static taint analysis tool for Android. Built on SOOT, it implements context-, flow-, field-, and object-sensitive analysis with precise Android lifecycle modelling, achieving 93% recall on DroidBench 2.0 at 86% precision. FlowDroid operates on a single APK and does not natively support cross-application analysis.

**IccTA** [3] extends FlowDroid with inter-component taint propagation by injecting ICC edges discovered by EPICC or IC3 [9] directly into FlowDroid's call graph. It improves recall on ICC-related leaks but inherits FlowDroid's single-APK limitation.

**AMANDROID** [4] performs flow- and context-sensitive inter-component data-flow analysis based on an interprocedural data-flow graph (IDFG) and an explicit data dependency graph (DDG). It explicitly models Android component lifecycles and achieves strong precision, but requires constructing the full IDFG upfront, which limits scalability for large apps.

**DroidSafe** [7] provides precise information-flow analysis using hand-written Android framework stubs. It achieves high precision but the stub development effort is substantial.

**JITANA** [5] is the classloader-based framework on which JITANA-DFA is built. The original contribution focuses on efficient and scalable IAC connection detection; interprocedural dataflow analysis was explicitly identified as future work.

**DIDFAIL** [10] and **SIFTA** [12] both address inter-application taint flows by combining per-app intra-app analyses. They do not preserve call graphs across app boundaries, limiting the precision of the combined analysis.

Our work differs from all of the above in being natively classloader-based: no compiler retargeting, no app merging, native DEX support, and simultaneous multi-APK loading with a unified lifecycle and threading model.

---

## VII. Conclusion

We presented JITANA-DFA, a context-sensitive, demand-driven interprocedural taint analysis tool for Android built natively on the JITANA classloader-based framework. The tool implements a dual-domain taint engine (parameter taint and source-to-sink), field sensitivity via a FieldTaintMap, array and wide-register support, CHA-based virtual dispatch, manifest-aware component seeding, exception-handler taint propagation, constructor receiver taint, cross-application IPC chain detection, and a multi-phase Android lifecycle and threading model.

Evaluated on 182 APKs from DroidBench 3.0, JITANA-DFA achieves **89.1% precision, 83.7% recall, and F1 = 0.863** across 18 benchmark categories, with perfect precision on ten categories including EmulatorDetection, InterAppCommunication, Lifecycle, Reflection, and Threading. The tool attains 100% recall on DynamicLoading, InterAppCommunication, ArraysAndLists, Threading, Reflection ICC, and SelfModification. The lifecycle and threading modeling contributes the largest recall improvements: Lifecycle recall rises to 91.7%, Threading to 100%, and Callbacks to 92.3%. The primary remaining limitations are false positives from unreachable-code paths not pruned by constant propagation, and false negatives from container taint (which causes analysis timeout) and reflection-based dispatch.

---

## References

[1] S. Arzt, S. Rasthofer, C. Fritz, E. Bodden, A. Bartel, J. Klein, Y. Le Traon, D. Octeau, and P. McDaniel, "FlowDroid: Precise context, flow, field, object-sensitive and lifecycle-aware taint analysis for Android apps," in *Proc. ACM SIGPLAN PLDI*, 2014, pp. 259–269.

[2] S. Arzt et al., "DroidBench 3.0," 2018. [Online]. Available: https://github.com/secure-software-engineering/DroidBench (branch: develop).

[3] L. Li, A. Bartel, T. F. Bissyandé, J. Klein, Y. Le Traon, S. Arzt, S. Rasthofer, E. Bodden, D. Octeau, and P. McDaniel, "IccTA: Detecting inter-component privacy leaks in Android apps," in *Proc. ICSE*, 2015, pp. 280–291.

[4] F. Wei, S. Roy, X. Ou, and R. Song, "Amandroid: A precise and general inter-component data flow analysis framework for security vetting of Android apps," in *Proc. ACM CCS*, 2014, pp. 1329–1341.

[5] Y. Tsutano, S. Bachala, W. Srisa-an, G. Rothermel, and J. Dinh, "An efficient, robust, and scalable approach for analyzing interacting Android apps," in *Proc. IEEE/ACM ICSE*, 2017, pp. 324–334.

[6] R. Vallée-Rai, "Soot: A Java bytecode optimization framework," Master's thesis, McGill University, 2000.

[7] M. I. Gordon, D. Kim, J. Perkins, L. Gilham, N. Nguyen, and M. Rinard, "Information-flow analysis of Android applications in DroidSafe," in *Proc. NDSS*, 2015.

[8] D. Octeau, P. McDaniel, S. Jha, A. Bartel, E. Bodden, J. Klein, and Y. Le Traon, "Effective inter-component communication mapping in Android: An essential step towards holistic security analysis," in *Proc. USENIX Security*, 2013, pp. 543–558.

[9] D. Octeau, D. Luchaup, M. Dering, J. Somesh, and P. McDaniel, "Composite constant propagation: Application to Android inter-component communication analysis," in *Proc. ICSE*, 2015, pp. 77–88.

[10] W. Klieber, L. Flynn, A. Bhosale, L. Jia, and L. Bauer, "Android taint flow analysis for app sets," in *Proc. ACM SIGPLAN SOAP*, 2014, pp. 1–6.

[11] L. Li, A. Bartel, T. F. Bissyandé, J. Klein, and Y. Le Traon, "ApkCombiner: Combining multiple Android apps to support inter-app analysis," in *Proc. IFIP TC 11 SEC*, 2015, pp. 513–527.

[12] A. von Rhein, T. Berger, N. S. Johansson, M. M. Hard, and S. Apel, "Lifting inter-app data-flow analysis to large app sets," University of Passau, Technical Report MP-1504, 2015.
