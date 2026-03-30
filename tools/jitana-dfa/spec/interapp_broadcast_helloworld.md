# Interapp Parameter Taint: HelloWorld via `sendBroadcast`

Two HelloWorld APKs — **HelloWorldSender** and **HelloWorldReceiver** — exercise
the simplest interapp taint path: a method parameter in the sender travels through
`sendBroadcast(Intent)` and arrives as the `Intent` argument of the receiver's
`onReceive`, where it can reach a downstream sink.

---

## Apps

### HelloWorldSender (`com.example.helloworldsender`)

| Element | Value |
|---------|-------|
| APK | `HelloWorldSender.apk` |
| Entry method | `Lcom/example/helloworldsender/MainActivity;.sendMessage(Ljava/lang/String;)V` |

`sendMessage(String msg)` is the taint source. It:
1. Creates a new `Intent` with action `com.example.helloworld.ACTION_HELLO`.
2. Calls `intent.putExtra("message", msg)` — tainted string flows into the Intent.
3. Calls `context.sendBroadcast(intent)` — tainted Intent exits the app.

### HelloWorldReceiver (`com.example.helloworldreceiver`)

| Element | Value |
|---------|-------|
| APK | `HelloWorldReceiver.apk` |
| Entry method | `Lcom/example/helloworldreceiver/HelloReceiver;.onReceive(Landroid/content/Context;Landroid/content/Intent;)V` |

`onReceive(Context, Intent)` is the interapp taint entry. It:
1. Extracts the string via `intent.getStringExtra("message")`.
2. Uses the value at a downstream sink (e.g., `Log.i`).

---

## Interapp Channel

```
sendMessage(String msg)          [HelloWorldSender]
    │
    ├─ intent.putExtra("message", msg)
    │
    └─► Context.sendBroadcast(intent)
                │
                │  action: com.example.helloworld.ACTION_HELLO
                │
                ▼
        HelloReceiver.onReceive(Context, intent)   [HelloWorldReceiver]
                │
                ├─ msg2 = intent.getStringExtra("message")
                │
                └─► Log.i(TAG, msg2)   ← sink
```

**Channel type:** `broadcast`
**Intent action:** `com.example.helloworld.ACTION_HELLO`
**Taint carrier:** `putExtra("message", …)` → `getStringExtra("message")`

---

## Intent Taint Model

Intent acts as a taint-carrying container. For this first implementation, use a
conservative whole-object approximation:

- **Taint in:** if any argument to `Intent.putExtra(key, value)` is tainted,
  mark the Intent receiver object as tainted.
- **Taint out:** if the Intent receiver object is tainted, every
  `getStringExtra` / `getIntExtra` / `getBundleExtra` / … call on it returns
  taint.

This avoids full field-sensitive key tracking at the cost of some imprecision.

---

## Analysis Phases

### Phase 1 — Sender

Run `run_interproc_param_taint` on **HelloWorldSender.apk**.

```
config.seed_public_only = false
config.lib_policy       = Conservative
config.sinks = [
    { Landroid/content/Context; sendBroadcast  (Landroid/content/Intent;)V },
    { Landroid/content/Context; sendOrderedBroadcast
          (Landroid/content/Intent;Ljava/lang/String;)V },
]
```

**Expected `SinkHit`:**

| Field | Value |
|-------|-------|
| caller | `Lcom/example/helloworldsender/MainActivity;.sendMessage(Ljava/lang/String;)V` |
| callee | `Landroid/content/Context;.sendBroadcast(Landroid/content/Intent;)V` |
| tainted_args | `[0]` (the Intent) |

### Phase 2 — Receiver

After phase 1, for each `SinkHit` at `sendBroadcast` whose Intent was tainted,
look up the matching `interapp_channel` by Intent action and seed the
`receiver_source` method.

Run `run_interproc_param_taint` on **HelloWorldReceiver.apk**.

```
config.seed_public_only = false
config.lib_policy       = Conservative
config.source_methods = [
    Lcom/example/helloworldreceiver/HelloReceiver;
        .onReceive(Landroid/content/Context;Landroid/content/Intent;)V
        tainted params: [1]   ← Intent
]
config.sinks = [
    { Landroid/util/Log;             i     (Ljava/lang/String;Ljava/lang/String;)I },
    { Landroid/util/Log;             e     (Ljava/lang/String;Ljava/lang/String;)I },
    { Ljava/lang/Runtime;            exec  (Ljava/lang/String;)Ljava/lang/Process; },
    { Ljava/io/FileOutputStream;     <init>(Ljava/lang/String;)V },
    { Landroid/webkit/WebView;       loadUrl(Ljava/lang/String;)V },
]
```

**Expected `SinkHit`:**

| Field | Value |
|-------|-------|
| caller | `Lcom/example/helloworldreceiver/HelloReceiver;.onReceive(…)V` |
| callee | `Landroid/util/Log;.i(Ljava/lang/String;Ljava/lang/String;)I` |
| tainted_args | `[1]` (the message string extracted from the tainted Intent) |

---

## Implementation Notes

**Bridge resolution.** After phase 1, for each `SinkHit` at `sendBroadcast`:
1. Recover the Intent action from the call site (static string or conservative unknown).
2. Match against registered `interapp_channels` by action.
3. Seed the matched `receiver_source` params before launching phase 2.

**Multi-app loader.** Load both APKs into the same Jitana `virtual_machine`
with distinct loader IDs so the shared class graph supports cross-app subtype
queries.

**Phase ordering.** Phases are sequential; phase 1 drives phase 2 seeding.
Fixed-point iteration is not needed for simple broadcast (no reply path).
For ordered broadcasts with `setResult`/`getResultData`, a second iteration
would be required.

---

## Current Implementation: How `sendBroadcast` Detection Works

This section documents the actual code path in
`lib/jitana/analysis/interproc_param_taint.cpp` that detects tainted
`sendBroadcast` calls.

### Step 1 — Sink Registration (`default_sinks`, line ~1246)

`sendBroadcast` and `sendOrderedBroadcast` are registered as sinks in
`default_sinks()` alongside `Log.i`, `Runtime.exec`, etc.:

```cpp
// Inter-App Communication — tainted data leaving the app
{"Landroid/content/Context;", "sendBroadcast",
 "(Landroid/content/Intent;)V"},
{"Landroid/content/Context;", "sendOrderedBroadcast",
 "(Landroid/content/Intent;Ljava/lang/String;)V"},
```

If `config.sinks` is non-empty these defaults are replaced; otherwise
`run_interproc_param_taint` uses this list verbatim (line ~1372):

```cpp
auto sinks = config.sinks.empty() ? default_sinks() : config.sinks;
```

### Step 2 — Sink Matching (`is_sink` lambda, line ~633)

At every `invoke-*` instruction the analysis calls `is_sink(callee_mid)`.
Matching is two-level:

1. **Exact class match** — `callee.type.descriptor == spec.type_descriptor`
2. **Subtype match** — BFS over the class graph collects all supertypes of the
   callee's class (cached in `CtxCache::supertype_cache`); if any supertype
   equals `spec.type_descriptor` the call is a sink.

This means a call on an `Activity` (which extends `Context`) also fires the
`sendBroadcast` sink without needing a separate spec entry.

### Step 3 — Taint State at the Call Site (`compute_summary_ctx`, line ~704)

When the dataflow fixpoint reaches an `invoke` instruction:

```
new_in[r]  — taint bitvector for register r entering this instruction
invoke->args — ordered list of physical registers holding the arguments
```

`maybe_report_sink` iterates the argument registers and checks whether
`new_in[arg_reg].any()` is true (i.e., any source parameter's taint bit is
set). If at least one argument is tainted, a `SinkHit` is recorded:

```cpp
SinkHit hit;
hit.caller       = mid;           // method containing the sendBroadcast call
hit.offset       = ig[v].off;    // bytecode offset of the invoke instruction
hit.callee       = callee_mid;   // Landroid/content/Context;.sendBroadcast…
hit.tainted_args = {0};          // arg 0 = the Intent object
sink_hits.push_back(hit);
```

For `sendBroadcast(intent)` there is one non-`this` argument (the Intent),
so `tainted_args = [0]` means the Intent object itself carries taint — which
happens because `putExtra` propagated the tainted string into the Intent
register via the `iput`/`invoke` taint rules earlier in the same method.

### Step 4 — Virtual Dispatch via CHA (line ~729)

The call graph (`cg.callees`) maps each call site to its resolved targets.
The analysis iterates all CHA targets and calls `maybe_report_sink` for each,
so a polymorphic dispatch site (e.g. through a `ContextWrapper`) still fires
the sink if any resolved target matches:

```cpp
auto targets_it = cg.callees.find(cs);
if (targets_it != cg.callees.end()) {
    for (const auto& tgt : targets_it->second)
        maybe_report_sink(tgt);       // CHA targets
} else {
    maybe_report_sink(invoke->callee); // static/fallback
}
```

### Step 5 — Deduplication (line ~1438)

After the full fixpoint, duplicate `SinkHit` entries (same caller + offset +
callee + tainted_args) are removed before the result is returned, so each
broadcast call site appears exactly once in the output even if it was visited
in multiple contexts.

### Summary Data Flow

```
sendMessage(String msg)
    │
    │  param_seed[v_msg].set(0)          ← parameter 0 is tainted
    │
    ├─ invoke putExtra("message", msg)
    │      new_in[v_intent] |= new_in[v_msg]   ← Intent register becomes tainted
    │
    └─ invoke sendBroadcast(intent)
           is_sink(Context.sendBroadcast) == true
           new_in[v_intent].any()        == true
           ──► SinkHit { caller=sendMessage, callee=sendBroadcast, tainted_args=[0] }
```

The Phase 2 seeding described above is **not yet automated**; currently a
`SinkHit` at `sendBroadcast` is the terminal output of phase 1, and the
analyst manually seeds the receiver's `onReceive` param 1 for phase 2.
