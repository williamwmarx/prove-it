# Rewriting Prove It's model checker in Rust

A design for a Rust model checker that is faster than today's Prove It and prints exactly what Java
TLC prints, staged so that every step ships on its own, is measurably faster, and is proven
identical to TLC and to the TypeScript checker before it is switched on.

Status: proposal. Nothing in the repository was changed. Every number marked *measured* comes from
the prototypes under `native/prototypes/` (section 10) on a local 4-core cloud machine
(Rust 1.97.0, Bun 1.4.4, Node 22.23.4). Those timings vary by about 10% between runs. Depot
numbers come from the benchmark of `main` at f284739 (run cb7zd2w63s), as summarised on the
headroom page.

---

## 0. Summary

**What to build.** Port Prove It's engine as it is today: interned value ids, expressions compiled
with footprints, and TLC's order. Do not write a new interpreter. tla-rs is a Rust interpreter, and
it is 16.5× slower than Prove It and cannot run 8 of the 18 suite models. The prototypes show what
Rust adds when it runs the *same* algorithms:

| Workload (measured, same algorithm in both languages) | TypeScript on Bun | Rust | Ratio |
|---|---|---|---|
| Interning (EXCEPT, a record, a set insert, a 3-element `setOf`, an append) per step | 274–311 ns | 159–174 ns | 1.7× |
| State-table probe ([hash, index] table, as `search.ts`) | ≈180 ns | ≈105 ns | 1.7× |
| Invariant `\A i, j \in 1..12 : i # j => ~(pc[i] = "cs" /\ pc[j] = "cs")` | 1.2–1.5 µs (monomorphic closures, the JIT's best case) | 2.0 µs as plain closures; **0.6–0.8 µs with fused nodes**; 0.13–0.16 µs as native code | 2× fused, ≈9× native |
| FP64 of a 5-integer state | 317 ns (interpreter path) | 15.5 ns | 20× |
| Process start | `bun -e 1`: 5.3 ms; bytecode binary on a one-state spec: 36 ms (Depot) | 1.45 ms | — |

So Rust is a constant factor of about 1.7–2× on the hot loops when the algorithm stays the same. It
does better than that in three places that matter: real threads over shared memory, no warm-up, and
compiled predicates. The staged path takes these one at a time.

**Staged path.** Every stage keeps the TypeScript checker as a fallback and as the oracle.

| Stage | What becomes Rust | Main gain (from the measured costs) | Projected suite geomean vs TLC (1 worker), today 6.6× |
|---|---|---|---|
| 1 | The engine core as an N-API addon: store, FP64, compiler, Init/Next walker, invariants, constraints, VIEW, symmetry, single-thread BFS, checkpoints. The TS front end, interpreter and CLI stay. | Large engine models 1.3–2× (store, probe, invariants, no JIT). Makes the AOT binary (16 ms start) as fast as the JIT one. | ≈8.7× (7.7–9.8×) |
| 2 | A deterministic multi-threaded search, batched liveness answers, parallel symmetry and VIEW | 2–3× on models over 0.5 s on 4 cores | ≈11.3× (10.3–12.3×) |
| 3 | Liveness on the engine's graph: tableau, SCCs, choosing the counterexample | ReadersWriters 0.38 → ≈0.10 s, TokenRing 0.54 → ≈0.16 s | ≈12.9× (11.6–14.3×) |
| 4 | A native front door: a Rust binary with the lexer, parser, resolver, level checker and SANY's success path. It hands anything unusual to the JS binary. | Small models from 50–150 ms down to 10–20 ms | ≈20× (17.6–24×) |
| 5 (optional) | The interpreter's slow paths: traces, errors, Print, TLCGet, `-continue`, `-dump`. TypeScript then stays only as the oracle. | Little speed. Removes the JS process from violation runs. | ≈ stage 4 |

**Parity harness.** Section 6 has the details. It has eleven layers, and the strongest four are new:
1. A **state-log differential**: each engine writes, for every state in BFS order, its parent,
   action and TLC fingerprint, and the logs must be identical.
2. **Store-op replay**: the TS store records every interning operation, Rust replays it, and the
   ids must match. The prototype already gives the same ids: 37,986 values and the same checksum
   over 2M steps.
3. A **value oracle** that drives TLC's own `Value` classes through a small Java helper, for
   order, fingerprints and comparison errors.
4. **Forced hand-over**: the engine stops at a random state, and the interpreter's continuation must
   print the same as a run without the stop.

The existing layers stay and gain a Rust backend: `conformance` over 823 recorded TLC outcomes,
the engine on/off sweep, the full-stdout differential against TLC, the unit tests, fuzzing,
`conformance:sany`, and the benchmark on Depot.

---

## 1. Scope and boundary

### 1.1 Options weighed

| Option | For | Against |
|---|---|---|
| A. Rust engine behind the TS front end and interpreter (N-API) | Smallest surface. The engine is about 9,000 lines in `src/engine/`. The fallback chain, the CLI and all of TLC's messages stay as they are. It ships in weeks, not quarters. | Startup and SANY stay in JS, so small models gain nothing. The front end has to serialise its input. |
| B. A Rust front end too | Removes the 30–50 ms of SANY and environment work on 2PCwithBTM | Gains nothing while a JS process still starts. A Rust SANY must reproduce SANY's messages for 1,873 modules. |
| C. An all-Rust CLI, TypeScript kept as the oracle | Largest startup gain | Needs the interpreter's slow paths in Rust (traces, every TLC error message, Print, TLCGet, `-continue`, `-dump`, liveness counterexamples). That is most of `values.ts`, `evaluate.ts`, `successors.ts`, `check.ts` and `liveness-checker.ts`, about 10,000 lines of exact semantics, for little speed: those paths run once per violation. |

**Choice: A first, then threads and liveness inside A, then a native front door that is B plus C's
process model, with the JS binary as its fallback process.** C's last step, porting the
interpreter, is left optional (stage 5). The reason is structural. A violation, an error, a
`Print`, or a trace through records TLC prints as `[a |-> 1]` and functions it prints as
`("a" :> 1)` is rare and short. It is also exactly where hash-consing loses information (section
2.8). The interpreter already handles all of it by replaying the path (`check.ts`
`resumeFromEngine`). Porting it buys parity risk, not speed.

### 1.2 The boundary in stage 1

```
 TS front end (unchanged)                         Rust (N-API addon, synchronous call)
 lexer/parser/resolve/levels/sany, config,
 environment, createTlcOrder
        |
        |  Engine IR: one Uint8Array (section 1.3)
        v
 check.ts tryEngine ------------------------------> prove_it_engine.check(ir, options, callbacks)
        |                                                 compile (or decline)
        |   <---- onInitialStatesStarted/onInitialStates/onProgress/onDebug (rare callbacks)
        |                                                 search
        |   <---- Result: complete | stopped(checkpoint) | declined(reason) | graph(+fps, live tables)
        v
 declined           -> TS engine (runEngine) exactly as today
 stopped            -> resumeFromEngine(decoded checkpoint) -> interpreter
 complete           -> counts, depth, outdegrees, fingerprint distance -> CLI messages
 complete with graph-> TS liveness checker (stage 1 and 2), Rust answers predicates in batches
```

The fallback becomes a three-step cascade: **Rust engine → TS engine → interpreter.**
- *Decline* happens before any state is produced. It covers a construct Rust does not compile yet,
  or a feature listed in `getEngineIneligibility`. Rust has emitted nothing, so the TS engine
  starts from scratch. The cost is building the IR and compiling it, a few milliseconds.
- *Stop* happens at run time: a violation, deadlock, TLC error, or a construct found unsupported
  only at run time. Rust hands a checkpoint to the interpreter, as the TS engine does today.
  `engine-coverage` turns "TS engine completes, Rust stops" into a gate (section 6.4), so Rust never
  covers less than the TS engine at run time.

N-API, not `bun:ffi`: the library and the scripts run under Node too (`scripts/run.ts` runs the
conformance scripts under Node). N-API is the one ABI both runtimes load. The crossing costs are
*measured* in section 10.1: 100–160 ns per call in Bun and 15–60 ns in Node. `bun:ffi` costs about
10 ns. So the interface is coarse: **one call per check**, a callback only for progress (at most
once a minute, plus twice around the initial states), and liveness predicates answered in bulk as
one bitmap per predicate (section 5.1), never one call per state.

### 1.3 The Engine IR (the contract that makes stage 4 possible)

Today `compile.ts` reads the TS AST and `Environment` directly (`getDefinition`,
`environment.builtins`, `environment.substitutions`, `isLocallyResolved`, constants as `Value`s).
Stage 1 adds a lowering, `src/engine/ir.ts`, that writes one versioned binary blob holding:
- the definitions reachable from Init, Next, the invariants, constraints, properties and VIEW.
  These are operator and function definitions with parameters, and bodies as tagged nodes:
  kind, children, source location, and resolution (local slot, definition index, builtin id,
  substitution);
- constants and TLC's startup values (`environment.startupValues`), in `transfer.ts`'s encoding;
- the TLC string order from `createTlcOrder` (`src/tlc/order.ts`), as a text table in rank order,
  so Rust's `str()` assigns the same ranks `values.ts` `getStringRank` does;
- TLC's variable order (`search.getTlcOrder()`, the `tlcOrder` input of `runEngine`);
- the model config: INIT, NEXT, invariants, constraints, action constraints, the properties the
  engine checks (`toEngineProperties`), VIEW, the SYMMETRY group as `NamedPermutation[]`,
  `checkDeadlock`, `isWarningEnabled` (it decides the assigned shortcut in `action.ts`), and the TLC
  version;
- for liveness: the next-state actions as TLC splits them (`spec.actions`) and the predicates and
  ENABLED atoms the tableau will ask about.

*Measured:* JSON of the whole parsed module is 38 KiB for Commit, 82 KiB for 2PCwithBTM and
221 KiB for btree. It takes 0.6–3.8 ms on a cold Bun (`proto/ir/ast-size.ts`). A binary IR of only
the reachable definitions should come in under 1 ms. This cost is the floor of stage 1's overhead
on small models.

The IR is the seam the later stages use. In stage 4 the Rust front end emits the same IR, and
**IR byte-equality between the TS lowering and the Rust front end** is the front end's first parity
test (section 6.10).

---

## 2. Data layout

### 2.1 Ids and the value store

```rust
#[repr(transparent)] pub struct Id(u32);          // FALSE = 0, TRUE = 1, EMPTY_SET = 2, EMPTY_TUPLE = 3

#[repr(u8)] pub enum Kind { Bool, Int, Str, Model, Set, Fcn, Tuple }   // KIND_* in store.ts, same numbers

#[repr(C)] pub struct Meta {    // 16 bytes per id: one cache line holds four
    kind: Kind,
    flags: u8,                  // IS_RECORD (Fcn with all-string keys), IS_INT_RUN (domain lo..lo+n-1),
                                // HAS_TYPED_MODEL, ...
    model_type: u8,             // the type char of a typed model value A_x, 0 if untyped (getModelType)
    _pad: u8,
    size: u32,                  // elements, pairs, or components
    payload: i32,               // Int: value; Str/Model: text index; composite: heap offset
    hash: u32,                  // the mixed hash, kept for rehashing and parallel probes
}

pub struct Store {
    meta: Arena<Meta>,          // append-only, never moves (2.6)
    heap: Arena<u32>,           // blocks: Set [e0..en) | Fcn [k0..kn, v0..vn) | Tuple [v0..vn)
    table: InternTable,         // [(hash, id)] pairs, open addressing; sharded in stage 2
    texts: TextTable,           // Box<str>, UTF-16 length, rank: i32 (-1 = unranked), kind (Str or Model)
    small_ints: [Id; 4353],     // -256..=4096, interned first, as resetStore does
    value_fp: Arena<ValueFp>,   // F(v): u64 and |v|: u32 per id, filled lazily (2.4)
}
```

The layout follows `src/engine/store.ts` on purpose:
- `resetStore` order: FALSE, TRUE, EMPTY_SET, EMPTY_TUPLE, then the small integers;
- `internBlock` and `internHashed`: the FNV-style fold `imul(h ^ w, 0x01000193)` seeded with
  `imul(kind + 7, 0x9e3779b1) ^ size`, then `mix`;
- `internScalar`;
- in-place lookups that copy nothing unless the value is new: `recordOf` with a `RecordShape`
  holding the hash prefix of its keys, and `internPatched` for EXCEPT.

With the same hashes and allocation order, Rust hands out **the same ids for the same sequence of
operations** in one thread. *Measured:* the 2M-step workload gives 37,986 values and checksum
−1720536883 in both `store.ts` and the Rust port (`proto/store-bench`). The store-op replay test
(6.6) depends on this. Rust's layout differs from TS's structure-of-arrays (`kinds`, `payloads`,
`sizes`, `hashes`) only where Rust can do better without changing ids:
- one 16-byte `Meta` read gets kind, size and payload in one cache miss;
- `IS_RECORD` and `IS_INT_RUN` are computed once at intern time. TS rescans for them in
  `isRecordId` and caches them per id in `classifyDomain`/`domainKinds`.

**TLC's order** is `store.ts` `compare`, ported exactly:
- booleans by id; integers by value;
- strings by rank, ranked before unranked, unranked by text (`compareTexts`);
- model values by rank, with typed values checked (`checkModelTypes`);
- an untyped model value is less than any other kind, and a typed one fails;
- sets by size, then element by element;
- functions and tuples by size, then keys, then values (`compareFunctions`). A record compared
  with a non-record function fails.

Rust keeps every place where `compare` or `equals` bails. Those are the places TLC throws:
- the walk to the first differing element in `equalsSets` and `equalsFunctions`;
- `isMember` checking the element against the first and last element of the set
  (`checkComparable`);
- `isSubset` still comparing after the sizes decide.

**Sets** are sorted, duplicate-free blocks in TLC order. They are built by `setOf`'s check whether
the input is already sorted, then insertion sort for runs of 16, merge above, and deduplication.
`union`, `intersection` and `difference` are linear merges that return an operand where the result
equals it. Membership uses `findInBlock`: subtraction for a run of consecutive integers, a linear
scan up to 16 elements, binary search by `compare` above that. **Functions** hold their domain in
TLC order, then their range. A domain `1..n` makes a `Tuple` (`functionOfSorted`, `internPairs`).
**Records** are `Fcn` with string keys. They differ from a string-domain function only in the
`IS_RECORD` flag derived from their content, as in TS. **Strings and model values** share the text
table, so a model value and a string with the same text get different ids but the same rank, as in
`model()` and `str()`. **Integers** are `i32`. TLC's overflow becomes a bail, as in `int()`.

### 2.2 States

A state is `[Id; W]`, W ids in the engine's variable order (`environment.variables`). TLC's
variable order is applied only where it matters: when fingerprinting, when comparing for symmetry,
and when encoding a checkpoint.

```rust
pub struct StateLog {                  // the states found, in TLC's BFS order: index = TLC's state number order
    width: u16,
    ids: Arena<Id>,                    // width ids per state
    parents: Arena<u32>,               // u32::MAX for an initial state
    fps: Arena<u64>,                   // TLC's FP64 of each state's key (2.3)
    actions: Option<Arena<u16>>,       // the action each state was first reached by, when liveness asks
    keys: Option<Arena<Id>>,           // VIEW value or symmetry representative, when it isn't the state
}
```
`search.ts` already keeps `states`, `parents` and `separateKeys` as flat `Int32Array`s, so this is
the same layout with 64-bit fingerprints added. Commit's 282,251 states of six ids take 6.8 MB.

### 2.3 The fingerprint set and the state table

Here stage 1 changes the algorithm while keeping TLC's semantics. Today the TS engine deduplicates
**by exact id vectors**: a `[hash, index]` table, then a comparison against `states`
(`search.ts` `findSlot`). After the search it recomputes **every** state's TLC fingerprint only to
print the collision-probability line (`getStateFingerprints`), which costs 4–10% of engine models.
TLC deduplicates **by FP64 fingerprint** in its FPSet.

Rust keys the table on **TLC's 64-bit fingerprint**: FP64 with `-fp 0`, of the state in TLC's
variable order, or of the VIEW value, or of the symmetry representative, as TLC fingerprints them.

```rust
pub struct FpSet {                       // stage 1: one shard; stage 2: 256 shards by the top 8 bits
    shards: Box<[Mutex<FpShard>]>,
}
struct FpShard { slots: Vec<u64>, len: usize, has_zero: bool }   // linear probing; 0 = empty, a real 0 kept in has_zero
// With a graph to record, slots are (fp: u64, index: u32) so an edge to a seen state finds its index.
```

Why:
- **Exact TLC semantics.** A real FP64 collision merges two states in TLC, and now in Rust as well.
  The TS engine would keep both. Collisions are astronomically rare (TLC prints the odds), but
  this is the right side to be on. It also removes the "wide strings" ineligibility: TLC folds
  characters to their low byte (`charCode & 0xff` in `tlc/fingerprint.ts`), so distinct strings
  can collide systematically. Today `getEngineIneligibility` sends such specs to the interpreter
  (`search.isFingerprintedLikeTlc`).
- **One random read per probe.** The id-vector table reads a slot and then the stored state, two
  misses. The fingerprint table reads one 8-byte slot.
- **The collision line for free.** The fingerprints exist during the search, and the minimum
  distance comes from sorting them once at the end. That is the 4–10% the headroom page counts,
  minus a sort.
- **The liveness checker's successor order** (`check.ts` copies `tlcFingerprints` before the TS
  liveness checker runs) comes straight from `StateLog.fps`.

The cost is one fingerprint per *generated* state, not per distinct state. It uses the linearity
`fingerprint.ts` already exploits. F(v) and |v| are kept per id. A state's fingerprint is
`shift(INIT, L) xor` the xor of `shift(F(v_j), S_j)`, and a successor that changes k values of
equal lengths costs k table shifts. *Measured* (`proto/store-bench`, mode `fp`): a full
recomputation for every probe, with an unoptimised shift (a hash-map lookup per shift), costs
298–329 ns per step. The id-vector table costs 260–305 ns. The two are level even before the
incremental trick, and both found the same 317,584 distinct states. `PROVE_IT_FP_VERIFY=1` also
stores the ids and asserts on every fingerprint hit that the states are equal. A failure is a real
collision. It is reported, and Rust carries on with TLC's behaviour. This flag runs on the corpus
in CI (6.7).

### 2.4 FP64

`u64` arithmetic replaces the `high`/`low` halves of `src/tlc/fingerprint.ts`. The tables are
built as `createByteModTable` builds them: the polynomial is `0x911498ae0e66bad6`, and the
`ByteModTable` comes from powers x^64..x^71. Value tags are BOOL 0, INT 1, STRING 3, SET_ENUM 5,
FCN_RCD 9 and MODEL 21. A model value's token is `getStringRank + 1`. A string is extended by its
UTF-16 length and then each code unit's low byte. *Measured:* the Rust port gives the same
fingerprint as `getTlcFingerprint` for a sample of ints, `-2^31`, a string, a boolean, a set, a
record and a tuple: −2179341659381351120. A million 5-integer states give the same xor. Rust takes
15.5 ns per state; the interpreter's path takes 317 ns.

### 2.5 The BFS queue

There is no separate queue. The `StateLog` is the queue: states `[expanding, levelEnd)` are the
current level, as in `runEngine`'s `for (expanding …; expanding === levelEnd …)`. TLC's "states
left on queue" is `stateCount − expanding − 1`, as `reportProgress` computes it. States are never
removed. The interpreter needs them for checkpoints and traces, and the TS engine keeps them too.
A model past RAM is out of scope, as it is today. Its TLC outcome would be an out-of-memory
"error", which conformance excludes for large models.

### 2.6 Memory that never moves

`Arena<T>` reserves address space up front (64 GiB on 64-bit hosts, committed page by page as it
is written), so readers on other threads never see a reallocation. This is what `store.ts`'s
`createGrowable` does with a 1 GiB `SharedArrayBuffer`. It is one small `unsafe` module over
`mmap`/`VirtualAlloc`. Single-threaded stage 1 could use `Vec`, but using the arena from the start
keeps stage 2 from changing the layout.

### 2.7 The graph for liveness

It is the same CSR shape as `EngineGraph` in `search.ts`:

```rust
pub struct Graph {
    successor_counts: Vec<u32>,      // per state: successors generated
    new_counts: Vec<u32>,            // per state: how many were new
    edge_offsets: Vec<u64>,          // edges of state i in [edge_offsets[i], edge_offsets[i+1])
    edges: Vec<u32>,                 // target state indices, in the order generated
    labels: Option<Vec<u16>>,        // the action position of each edge, when ENABLED asks per action
}
```
With `StateLog.fps` this is everything the TS liveness checker reads today through
`createLiveOracle` (`live.ts`) and the `tlcFingerprints` that `check.ts` fills. It is also the input
of the stage-3 Rust liveness checker. `MAXIMUM_GRAPH_STATES` (4M) stays as the point where the
engine hands its graph over.

### 2.8 Why the engine never prints values

Hash-consing makes a record and a string-domain function with the same pairs **one id**. It does
the same for `<<a, b>>` and a function over `1..2`. TLC prints them by how they were built, and
`transfer.ts`'s `FUNCTION_CLASSES` ("lambda", "tuple", "record") exist to carry that. TLC keeps the
first-found *state* object. A hash-consed store keeps the first-built *value* anywhere in the run,
which can differ. So, as today, the engine produces only *which* states and *in which order*. The
interpreter re-executes the path to the state it resumes from (`resumeFromEngine`: "TLC prints a
function by how it was built") and prints. Section 5 relies on this rule.

---

## 3. Expression evaluation

### 3.1 How compiled expressions run

There were three candidates. The prototype (`proto/store-bench/src/eval.rs`, section 10.4)
*measured* each on the same invariant over 4,096 states:

| Form | ns per evaluation |
|---|---|
| TS closures as `compile.ts` builds them (monomorphic: the JIT inlines them) | 1,227–1,457 |
| Rust closures, one node per AST node (`Box<dyn Fn>`) | 1,804–2,366 |
| Rust closures with **fused nodes** | **590–779** |
| Rust stack bytecode, a naive `match` loop | 3,318–4,488 |
| Native Rust (the ceiling for Cranelift) | 124–160 |

Conclusions:
1. A naive bytecode VM loses to closures in Rust. The dispatch `match` plus operand-stack traffic
   costs more than an indirect call the CPU predicts. A register VM could close that gap only with
   threaded dispatch, which stable Rust does not guarantee. So: no VM.
2. Plain Rust closures lose to JSC on monomorphic code. The real engine's closure call sites are
   megamorphic (one `evaluate` slot per node kind, called with thousands of closures). That is the
   "megamorphic calls and deoptimisation" cost the headroom page names, so the TS figure above is
   its best case.
3. **Fused nodes**, closures chosen by pattern that do several AST nodes of work per call, are 2–3×
   faster than plain ones and about 2× faster than TS's best case. This is what `codegen.ts`'s
   `emit` does for Init and Next in JS ("a guard an `if` whose condition is the guard's own code").
   In Rust it applies to every predicate, invariants included. Today invariants are 22–61% of
   engine models and remain closure trees in TS.

**Stage 1: closures with fused nodes.** The compiler (`native/crates/tla-engine/src/compile/`)
mirrors `createCompiler` kind by kind:
- `Identifier`, `Apply` (operators expanded at the call site with arguments bound, as TLA+
  defines and as `compile.ts` does; a recursive operator or function compiled once and called by
  value);
- `If`, `Case`, `Let`, `Forall`, `Exists`, `Choose`, `SetEnumeration`, `Tuple`, `Record`;
- `FunctionApplication`, `FieldAccess` (with the `applyField` position hint), `Except`, `ExceptAt`
  (`exceptAt`), `FunctionConstruction`, `SetFilter`, `SetMap`, `FunctionSet`, `RecordSet`,
  `Product`, `Unchanged`, `Enabled`;
- the operators in `binary`/`compileNativeBuiltin`, from `=` and `\in` to `\o`, `Seq`, `Assert`,
  `SelectSeq`, `Cardinality`, `:>` and `@@`.

The fused set starts from what the profiles show is hot:
- `VarEqConst(var, id)`: `x = c`;
- `ApplyVar(var, slot)`: `f[i]` with `f` a variable and `i` bound;
- `FieldOfVar(var, key, hint)`;
- `MemberConst(slot, set)`;
- `ForallInterval`/`ExistsInterval(slot, lo, hi, body)`, as TLC keeps intervals
  (`getKeptInterval`);
- `ExceptVarAt(var, key, value)`;
- `CardinalityFilter`;
- `AndAll`/`OrAny` over n children, which check booleans as `checkBoolean` does.

```rust
pub type Eval = Box<dyn Fn(&mut Regs) -> Result<Id, Stop> + Send + Sync>;
pub struct Regs<'a> {                    // compile.ts's CUR, NXT, LOC, EPOCH and registers.assigned
    cur: &'a [Id], next: &'a mut [Id], locals: &'a mut [Id], epoch: u64, assigned: u32,
    memo: &'a mut MemoTables,            // per thread (3.2)
}
pub struct Compiled { eval: Eval, footprint: Footprint, is_costly: bool, is_normalized: bool,
                      is_enumerated: bool, are_elements_enumerated: bool, is_boolean: bool,
                      order: Option<Enumerator> }      // the `reference` of compile.ts, made native (3.3)
```

**Later tier (after stage 2, behind a flag): Cranelift** for predicates and actions whose
cumulative time passes a threshold. They compile on a background thread and swap in at a level
barrier. This keeps the start-up advantage, since short runs never compile, while long
invariant-heavy runs (LamportMutex, Bakery, SingleNode, btree) get closer to the native row (4–5×
over fused closures). It adds a few megabytes to the addon. It is not on the critical path: the
fused-closure figures above are enough for stages 1–4.

### 3.2 Footprint memoisation

The port is semantic-for-semantic:
- `Footprint { vars, primes, slots }`, computed at compile time and merged sorted
  (`mergeFootprints`, `withoutSlots`);
- `cached()`: a width-0 expression is evaluated once. A costly expression of width 1–6 gets a
  `MemoTable` keyed by the ids in footprint order, current variables then primed variables then
  slots (`keyCodes`, `createProbe`). Wider expressions with no primes go to the `EpochCache`
  (`cachedInEpoch`, `EPOCH_KEYS` slot keys, valid while the current state keeps its epoch);
- `memo.ts`'s tables: width 1 is a direct array indexed by id while dense (`DIRECT_SPARSITY` 16,
  `DIRECT_MINIMUM` 2^16, `DIRECT_MAXIMUM` 2^23). Widths 2–6 are open addressing. After
  `PROBATION` (8,192 lookups) a table that hits less than `MINIMUM_HIT_RATE` (0.2) switches off.
  `MAXIMUM_ENTRIES` is 2^22.

Two Rust refinements change no results. Keys of width ≤ 2 pack into one `u64`, so a probe is one
compare. Values are written only after a successful evaluation (`lookupN` stores nothing on a
bailout), and this falls out of `?`: an `Err` returns before the store. The epoch counter is a
`u64` that is never reused (`nextEpoch`). `PROVE_IT_EPOCH_CHECK=1` re-evaluates on every epoch hit
and throws if the value differs, as `epochLookup` does. Memo tables are **per thread** in stage 2.
They cache pure functions of their keys, so sharing them cannot change a result, and per-thread
tables need no synchronisation.

### 3.3 Lazy sets

`compile.ts` keeps TLC's distinction between normalised sets, which TLC enumerates in its order,
and sets TLC keeps lazy (`isNormalized`, `isEnumerated`, `areElementsEnumerated`). For lazy sets
the TS engine asks the **interpreter** for the order: `reference` thunks rebuild the interpreter
`Value`, `compileOrdered` calls `getStreamedElements` or `getQuantifierElements`, and the result is
converted back with `fromValue` and cached as a tuple. Rust cannot call back into JS per
enumeration (100+ ns per crossing and a value conversion), so stage 1 ports TLC's enumerators as
native `Enumerator`s, one per lazy kind:

| Lazy set | TLC class | Order to reproduce (from `values.ts`) |
|---|---|---|
| `SUBSET S` | SubsetValue | TLC's subset enumeration order (the interpreter's `streamElements`) |
| `[S -> T]` | SetOfFcnsValue | as the interpreter enumerates `FunctionSet` |
| `[a : S, b : T]` | SetOfRcdsValue | field order by TLC's string order, odometer as `RecordSet` |
| `S \X T` | SetOfTuplesValue | as `ProductSet` |
| `UNION S` | UnionValue | **streams duplicates** until cached (`getStreamedElements`: "an element that two of them share comes up once for each") |
| `S \cup T` and friends, lazily | SetOperation | streamed as the interpreter's `SetOperation` |
| filters and maps over the above | — | composed |
| `Nat`, `Int`, `STRING`, `Seq(S)` | infinite | enumerating them is a bail, as `infiniteSet` |

Each enumerator lands only with an **enumeration oracle** test (6.8): for generated small sets,
Rust's sequence must equal `getStreamedElements` and `getQuantifierElements` in TS, and TLC's own
enumerator through the Java helper. Until a kind lands, Rust **declines at compile time**, so the
TS engine runs the model as it does today. The pure builtins the TS engine bridges to the
interpreter (`PURE_BUILTINS`: SubSeq, SelectSeq, IsFiniteSet, Permutations, SortSeq, the Bags
operators) are ported the same way. ToString declines, because it needs TLC's value printer
(2.8).

### 3.4 Exact error and bail semantics

The engine **never prints a TLC message**. It only has to stop on every condition under which TLC
would do something other than continue. The interpreter then re-expands from the last good state
and prints exactly what TLC prints. Two rules follow:
1. **Completeness.** Rust stops wherever TLC errors on the path TLC evaluates. The cases are:
   - every `bail` in `store.ts`: incomparable values, typed model values, a record compared with a
     function, EXCEPT outside the domain, integer overflow, applying outside the domain;
   - every `bail` in `compile.ts`: a non-boolean condition, CHOOSE with no element, division by
     zero, a modulus by a non-positive number, a negative exponent, Head and Tail of an empty
     sequence, enumerating an infinite set, a failed Assert, a function over a non-set;
   - every `bail` in `action.ts`: an incomplete state, a guard that isn't a boolean, `x' \in S`
     with S not a set.

   The port keeps one table of reasons with the TS texts verbatim. They are not output, but
   `engine-coverage.ts` buckets by them (`normalizeReason`), so identical text keeps TS and Rust
   coverage tables comparable.
2. **No extra laziness, harmless extra eagerness.** If Rust evaluates something TLC would not, such
   as a memoised subexpression, the result is pure, so it is the same value. If that extra
   evaluation fails, Rust stops and the interpreter does the step properly. That costs speed, not
   parity. Rust must never *skip* an evaluation TLC performs that can fail. The short-circuit
   rules (`/\`, `\/`, `=>`, IF, CASE) are ported exactly from `compile.ts`.

```rust
pub enum Stop {
    Bail { kind: BailKind, reason: Reason },  // Unsupported | TlcError | Violation(InvariantKind) | Deadlock | GraphTooLarge
    Found,                                    // ENABLED's first successor (createEnabledTest's FOUND)
}
```
`Result<_, Stop>` replaces the thrown `Bailout`. There is no unwinding, and an `Err` crosses a
memo wrapper without writing it. Deep TLA+ recursion would overflow the native stack, so the
evaluator counts its depth and stops with `Unsupported("recursion too deep")` well before the
search thread's 256 MiB stack runs out. The interpreter then reproduces TLC's own failure. A Rust
`panic` is a bug. `catch_unwind` at the N-API boundary turns it into an `EngineInvariantError`, as
`check.ts` treats a non-Bailout error today: it reports and falls back. CI fails on any such
`[engine]` line.

### 3.5 Init and Next in TLC's exact order

The walker is `action.ts`'s design in continuation-passing form:

```rust
pub type Step = Box<dyn Fn(&mut Regs, &mut dyn FnMut(&mut Regs) -> Result<(), Stop>) -> Result<(), Stop>>;
```
It ports these rules one by one, each a named test:
- **Conjunctions** (`compileConjunction`): conjuncts run left to right, each a guard, an
  assignment, an UNCHANGED, or a branch. A branch continues through the conjuncts after it
  (`continuations`, `pending`). Each conjunction unassigns its own variables on the way out
  (`undoStack`).
- **The assignment rule** (`toConjunct`): `x' = e` assigns at the first conjunct where `x'` is
  unassigned, and is an equality test with `equals`'s bails after that. In Init the unprimed
  variable is assigned (`target(isInit)`). Assignment goes through operator arguments and
  zero-arity definitions (`getAssignableIndex`). `UNCHANGED <<…>>` assigns or tests each variable
  (`getUnchangedIndices`).
- **The assigned shortcut** (`isAssignedShortcut`): once every variable has a value, TLC evaluates
  the remaining conjuncts instead of walking them. It always does so in Init, and in Next only with
  warnings on. Rust keeps `shortcuts.isPastWalk`, because the liveness oracle's ENABLED is exact
  only when no shortcut passed a walk (`isEnabledExact`).
- **`x' \in S`** (`compileMembership`): elements in TLC's *streamed* order (`compileOrdered(…,
  "streamed")`). This is where UNION's duplicates come from.
- **Disjunction**: branches in order.
- **`\E`** over several bounds: TLC's `ContextEnumerator` varies the *first* bound fastest
  (`frames`, `pushFrame`). An empty set short-circuits.
- **IF, CASE, LET** (`bindLet`), operator application, the lazy function application TLC walks
  (`resolveLazyApplication`), and universal quantifiers with assignments
  (`compileWalkedForall`).
- **ENABLED** (`createEnabledTest`): runs the step on a private next state until the first
  successor (`Stop::Found`), and restores the outer next state and assignment state.
- **Per path, statically known assignments**, as `codegen.ts` writes them out (`UNASSIGNED`,
  `ASSIGNED`, `UNKNOWN`): the compiler specialises a conjunct to "always assigns" or "always
  tests" where the path decides it, and checks at run time otherwise.

The search loop is `runEngine`'s, step for step:
- *Initial states:* complete the state; check constraints; compute the key and look it up; if
  unseen, check the initial invariants and initial predicates, then add the state.
- *Each successor:* check every successor is complete; check constraints with
  `holdsAllChanged`; compute the key; check the action constraints; look the key up. If the state
  is not in the model, **or** it is new, check the invariants. That is TLC's rule: a state outside
  the constraint is still checked. Then record the edge, check the action properties, and add the
  state if new.
- Deadlock when no successor exists and `checkDeadlock` is set.
- The out-degree histogram over 32 buckets, and the depth.

---

## 4. Parallelism

### 4.1 Design: level-synchronous, keyed by (parent, step)

The TS parallel search (`parallel.ts`) already has the right algorithm. What it lacks is cheap
threads: each worker re-parses the spec and warms its own JIT (`engine-worker.ts`). It is opt-in,
does not beat one thread on runs of a few seconds, and is disabled under VIEW, symmetry and graph
recording (`canShare` in `search.ts`). Rust keeps the algorithm and removes those limits.

1. A BFS level `[start, end)` of the `StateLog` is split into chunks of 16–64 states, claimed with
   an atomic cursor (work stealing, as `CURSOR`/`CHUNK`).
2. A thread expanding state `p` numbers its successors `s = 0, 1, …` in the order the walker
   generates them. For each successor it computes the key and its FP64 and probes the `FpSet`:
   - found from an **earlier level**: a duplicate. Generated count +1, nothing else, except the
     per-step checks (action constraints, action properties, the graph edge) and the invariant
     check for a state outside the model, all of which depend only on this step;
   - found as a **candidate of this level**: the candidate keeps the occurrence with the smallest
     key `(p << 32) | s`, together with that occurrence's own payload: the ids of the concrete
     state it reached and the result of its invariant check. Under VIEW or symmetry two different
     concrete states share one fingerprint, as `getKey` and `addState` in `search.ts` keep the
     state apart from its key, so the payload must follow the key: replacing only the key would
     give the earlier parent the later occurrence's state, and the next level would expand the
     wrong one. The candidate's slot is a small lock (or a pointer to an occurrence record swapped
     with compare-and-swap on the key), so the key and its payload change together;
   - absent: insert a candidate holding the fingerprint, the ids, key `(p, s)`, and the result of
     the invariant check, which is a pure function of the state, so any thread can compute it.
3. At the barrier the coordinator sorts the candidates by key. That is the order TLC's single
   worker queues them: it dequeues parents in order and generates successors in order, so the
   first occurrence of a state is its smallest (parent, step). The candidates become states
   `end, end+1, …` with `parents[i]` taken from the key and each state's ids and invariant result
   from the winning occurrence. Without VIEW or symmetry every occurrence of a fingerprint is the
   same state, so the payload never changes and the lock is never taken. `newCounts` and the out-degree histogram
   come from the winning keys. The generated count is a sum. The depth is the level number.
4. Levels smaller than a threshold (2,048 states, as `MINIMUM_SHARED_LEVEL`) run on the
   coordinator alone, so short runs never pay for a barrier.

The counts, depth, out-degrees, state numbering, parents and therefore traces are the same as one
TLC worker's **for any number of threads**. The state log is a pure function of the previous
level's ordered list.

Stage 2's acceptance includes the case that breaks a key-only update: a spec whose VIEW (and one
whose SYMMETRY) maps different concrete states reached from two parents of one level to one key,
run with the thread holding the later parent forced to insert first. Its state log and output must
equal one thread's. The state-log differential also runs with 1 and 4 threads on every VIEW and
SYMMETRY model in the corpora.

### 4.2 Stopping exactly where TLC stops

Today a worker that stops makes the coordinator redo the whole level alone (`searchInParallel` →
`reloadFrom`). Rust stops exactly instead:
- every stop event (violation, deadlock, TLC error, run-time unsupported) carries its parent `p`
  (and step);
- an atomic `stop_at = min(stop_at, p)`. Threads skip chunks at or after `stop_at` but **finish
  every chunk before it**, since an earlier parent can still produce an earlier event, which lowers
  `stop_at`;
- once all chunks before `stop_at` are done, the checkpoint is everything TLC had found before
  expanding `p`: the earlier levels, plus this level's candidates with parent < `p`, sorted. The
  counts are those before expanding `p`. The interpreter re-expands `p`, as `resumeFromEngine`
  does with `checkpoint.expanding`.

TLC's single worker would have met exactly that event at exactly that point, so the interpreter
prints exactly TLC's report.

### 4.3 Shared structures

- **Store:** sharded intern table (256 shards by hash bits). Each shard is a `Mutex` around open
  addressing; a probe and insert takes about 50 ns, and with 256 shards contention is negligible.
  `Meta` and the heap are written before the id is published under the lock. That is the protocol
  of `store.ts`'s shared mode ("A value is written before its id is published under the lock").
  Reads are lock-free because the arenas never move. **Ids are no longer deterministic across
  threads** but nothing observable depends on them: order is `compare`, never id order, and the
  level sort uses keys. `with N values` in the debug line becomes nondeterministic, which is
  acceptable for a debug line. The store-op replay (6.6) runs single-threaded.
- **Texts created at run time** (ToString, string concatenation) go through a locked text table.
  The rank is TLC's for a known text and −1 otherwise (`peekRank`), so order still never depends on
  creation order. TS bails here instead ("a string built while workers run").
- **Memo tables, registers, undo stacks, scratch:** per thread.
- **Symmetry image caches:** per thread at first (`createCanonicalizer`'s `images` per
  permutation), later shared with atomic publish.

### 4.4 Expected gain

TLC itself goes from 3.99 s to 1.97 s on Commit with four workers. Rust's search shares memory,
stays level-synchronous, has no per-worker warm-up, and has a serial part per level (the sort and
appending to the log) of O(n log n) on the candidates. With those properties it should reach
**2.5–3× on 4 cores for levels over about 10k states**. Overall that is **2–3× on models over
0.5 s** (Commit, btree, SimpleRegular, Bakery, LamportMutex, SingleNode, Paxos) and nothing on
short runs, by design. The things that limit it are memory bandwidth on the FpSet and the store,
per-thread memo warm-up (Commit has only 7,085 values, so it is small), and depth: Commit has 23
levels, so barriers are rare.

---

## 5. Liveness, symmetry, VIEW, constraints, deadlock and traces, `-continue`, `-dump`, TLC operators

| Feature | Stage 1 | Stage 2 | Stage 3 | Stage 4 | Stage 5 | Hand-over |
|---|---|---|---|---|---|---|
| CONSTRAINT, ACTION_CONSTRAINT | Rust | Rust, parallel | | | | — |
| INVARIANT, `[]P`, `[][A]_v`, initial predicates (`toEngineProperties`) | Rust detects; TS prints | parallel | | | | checkpoint at the violating state's parent |
| Deadlock | Rust detects; TS prints | parallel | | | | checkpoint at the deadlocked state |
| Violation and error traces | TS interpreter replays the path and prints | | | | Rust trace renderer | checkpoint (5.2) |
| VIEW | Rust (fingerprint of the view value) | parallel (TS can't) | | | | checkpoint carries `keys` |
| SYMMETRY | Rust port of `createCanonicalizer` | parallel | faster canonical form, proven equal | | | checkpoint carries representatives |
| Liveness (`PROPERTY` with `<>`, `~>`, fairness) | Rust records graph and fps, answers predicates in bulk; TS checks | parallel graph recording | **Rust tableau and SCCs**; TS prints the counterexample | | Rust prints | graph + fps + bitmaps (5.1) |
| `-dump`, `-continue` | TS interpreter (engine-ineligible today) | | | | Rust | not eligible |
| Print, PrintT, TLCGet, TLCSet, RandomElement, Any, JavaTime | decline → TS engine declines → interpreter | | | | Rust | decline |
| TLCEval | Rust (identity, as `compile.ts`) | | | | | — |
| ToString | decline (needs TLC's printer) | | | | Rust | decline |
| `_POSSIBLE`, periodic liveness, TLC 1.7.4 | ineligible, as `getEngineIneligibility` | | | | | — |
| Assumptions (ASSUME) | TS (checked before the engine, `findViolatedAssumption`) | | | Rust (front door) | | — |

### 5.1 Liveness across the boundary

Today `createLiveOracle` (`live.ts`) answers the interpreter's liveness checker one question at a
time, through `environment.liveOracle` in `evaluateLive` (`liveness.ts`). Each question is "does
predicate P hold of state s", "does action A hold of step (s, t)", or "is A ENABLED in s", and the
interpreter maps its `Value[]` back to an index through a `WeakMap`. Across N-API that would be one
crossing per (predicate, state). At about 150 ns in Bun, ReadersWriters' 21k states times a
handful of predicates would cost tens of milliseconds. So in stages 1–2 the TS side asks once per
predicate:
- `liveStateTable(predicateId) -> Uint8Array`: one byte per state, `0`/`1`/`2 = unknown` (the
  interpreter evaluates it, exactly as when `live.ts` returns `undefined`);
- `liveEdgeTable(actionId) -> Uint8Array` over `edges`, and `enabledTable(atomId)` from the edge
  labels when the ENABLED atom is made of TLC's actions (`findActionPositions` in `check.ts`),
  following `isEnabledExact`.

Rust fills each table in one pass over the `StateLog`, in parallel in stage 2. The TS oracle
becomes array reads, so the only crossings left are one per distinct predicate.

In stage 3 the tableau (`tableau.ts`), the product graph and the SCC search with TLC's
counterexample choice (`liveness-checker.ts`) move to Rust. They run over integer arrays: product
nodes are `(state: u32, tableau: u16)` packed in a `u64`, the SCC search is an iterative Tarjan,
and successors are ordered by `StateLog.fps` as the TS checker orders them by TLC fingerprints.
Rust returns either "holds" or the lasso as state indices plus the loop start. TS replays and
prints it, as `check.ts` already does for a reduced state space ("finds its actions again").

### 5.2 Run-time hand-over (any stop)

The checkpoint is `EngineCheckpoint` as `search.ts` defines it: `expanding`, `count`,
`generated`, `initialGenerated`, `outDegrees`, `states`, `parents`, `width`, and `keys` and
`keyWidth` under VIEW or symmetry. **States are encoded in `transfer.ts`'s format**
(`EncodedStates { words, strings, count }`), which TS decodes with `createStateDecoder`. TS ids
mean nothing to Rust, and vice versa. Rust writes every value reachable from the checkpoint's
states once, bottom-up, so decoding is linear in the number of distinct values. Records are tagged
as records and tuples as tuples, using the `IS_RECORD` flag and the `Tuple` kind. That is what
`convert.ts` `toValue` does today with `createSortedRecord`/`createTuple`. The interpreter then
runs `resumeFromEngine` unchanged, except that it decodes instead of calling `toEngineValue`. It
re-executes the path to `expanding`, so printing reflects how TLC built each value.

### 5.3 Symmetry

Stage 1 ports `createCanonicalizer`. For each permutation it caches each id's image in a
`Vec<Id>` indexed by id, and takes the representative as the smallest image compared variable by
variable in TLC's order, stopping early once the comparison exceeds the current smallest. That was
31% of Paxos in the profile. Rust makes the loop cheaper, about 1.7×, but the headroom page is
right that the real gain is algorithmic: a canonical form that sorts once instead of trying every
permutation. Any such form must give **the same representative** as the brute force, because the
representative's fingerprint decides deduplication. So it lands only with
`PROVE_IT_SYMMETRY_CHECK=1`, which computes both for every state on the corpus's SYMMETRY models
and on generated ones, in CI (6.7).

---

## 6. The parity harness

Principle: **TLC is the oracle for outcomes and output, and the TypeScript checker is the oracle
for everything internal.** Each layer below says what it compares, against which oracle, at what
granularity, and which script it extends.

| # | Layer | Compares | Oracle | Catches | Runs |
|---|---|---|---|---|---|
| 6.1 | Recorded outcomes | status, violation, counts, depth, trace length | TLC (expected.json, 823) | any outcome change | PR (smoke), main (all) |
| 6.2 | Full-stdout differential | normalised stdout+stderr+exit code, default and `-tool` | TLC live/recorded, TS | messages, traces, order of output | PR (smoke), main |
| 6.3 | State-log differential | per state: index, parent, action, FP64 | TS engine | order, the assignment rule, enumeration order, dedup | main, nightly |
| 6.4 | Engine matrix (on/off) | outcomes and coverage per backend | interpreter | wrong answers, coverage regressions | main |
| 6.5 | Unit-test parity | the 2,860 unit tests with `BACKEND=rust`; store/fp tests through a native facade | TS | API-level behaviour | PR |
| 6.6 | Store-op replay | id per interning operation | TS store | hashing, compare, set order, EXCEPT | PR (10 models), main |
| 6.7 | Self-checks | memo on/off, epoch check, FP verify, symmetry check, threads 1–16 | itself and TS | staleness, collisions, nondeterminism | main, nightly |
| 6.8 | Value and enumeration oracle | compare, equals, fingerprint, toString, enumeration order, errors | TLC's Value classes (Java helper) | value semantics | nightly (Depot, live TLC) |
| 6.9 | Spec fuzzing | stdout of generated specs | TLC live | everything above, combined | nightly |
| 6.10 | Front-end parity (stage 4) | IR bytes; SANY messages | TS front end; sany.json | front-end drift | PR, main |
| 6.11 | Forced hand-over | stdout with a stop at a random state vs without | itself | checkpoint and resume bugs | main |

### 6.1 Recorded TLC outcomes: extend `conformance.ts` and `check-model.ts`

- `check-model.ts` takes `PROVE_IT_ENGINE_BACKEND` from its environment (`ts`, `rust`, `auto`) and
  passes it to `check()`. It returns the backend that completed and the `[engine]` line, as
  `engine-coverage.ts` extracts it, so `.results.json` says who produced each verdict. With
  `--threads N` it sets `PROVE_IT_WORKERS`.
- `conformance.ts` takes `--backend` and `--threads`. `--check` fails if any model in
  `passing.json` no longer matches **for the backend under test**, so the passing set is the same
  for `ts` and `rust`. A new `--compare-backends` mode runs each model under both and fails on any
  difference in `ModelOutcome`, not only against TLC. That catches agreeing-but-wrong cases where
  TLC's recording has no counts (status `error`).
- `compare-outcome.ts` gains a `fingerprintDistance` field. TLC's "based on the actual
  fingerprints" line depends on *every* state's fingerprint, so it is a cheap whole-state-space
  check. `record-tlc.ts` already runs TLC with `-workers 1 -nowarning -seed 4 -fp 0 -lncheck final
  -noGenerateSpecTE`. It should also store the parsed collision line in `expected.json`, which
  means re-recording once at the pinned `TLC_COMMIT`.

### 6.2 Full-stdout differential: new `scripts/differential.ts`

It runs the **CLI binaries**, not the library: `dist/prove-it` with the TS engine, with the Rust
engine on 1 thread and on 4, with the engine off (`PROVE_IT_ENGINE=0`), and Java TLC from the
pinned jar with `record-tlc.ts`'s flags. All run on the same model and argv, once in default
output and once with `-tool`. It captures stdout, stderr and exit code (`exit-codes.ts`).

**Normalisation** is one module, `scripts/normalize-output.ts`, built from `getSteadyLines` and
`STARTUP_LINE` in `tests/unit/cli.test.ts`. That test then imports it, so tests and runner share
one definition. It rewrites:
- dates (`\d{4}-\d\d-\d\d \d\d:\d\d:\d\d`) and ` in \d\ds at `;
- the pid (`[pid: N]`), heap and offheap MB, core count, and the OS and runtime part of the
  `Running breadth-first search …` line;
- the `/tmp/tlc-N/` directory in `Parsing file` lines and the `-metadir`;
- the `TLC2 Version` line;
- in `-tool` mode, the timing payloads of the progress messages; message codes and classes are
  kept.

`Progress(...)` lines are emitted on a timer (`PROGRESS_INTERVAL`, 60 s), so their *presence*
varies. The normaliser drops whole progress lines, and the counts inside them are tested separately
by 6.3. The normaliser must never touch counts, state lines or messages. A unit test feeds it TLC
output with deliberate count changes and asserts that they survive.

**Gates:**
- **TS vs Rust (any thread count):** byte-identical after normalisation, zero allowed
  differences.
- **TLC vs Prove It:** against `tests/conformance/known-differences.json`, one justified entry per
  model with the expected diff hunk. The gate is "no new differences". The current state is
  recorded once with the TS checker before any Rust lands (milestone M0), so the baseline is
  today's parity, not an aspiration.

TLC's outputs are recorded with `record-tlc.ts --stdout` into a content-addressed cache keyed by
`TLC_COMMIT` and the model's file hashes. On Depot it is an artifact; locally it is
`tests/conformance/.tlc-stdout/`. PR runs then need no JVM. `parity.yml` re-records on a cache
miss.

### 6.3 State-log differential: new, the backbone for internal parity

`PROVE_IT_STATE_LOG=path` makes the TS engine (`search.ts`) and the Rust engine each write one
record per state in TLC order: `(index, parent, action label, FP64 of the key)`. Optionally it
also writes `(generated so far, outdegree)` at each expansion, which catches count drift before it
shows in the totals. The TS engine computes fingerprints after the search (`getStateFingerprints`),
so its log is written there. Rust writes its own as it goes.

`scripts/state-log-diff.ts` reads two logs and reports the first differing index. It decodes both
states, and the parents, through a checkpoint at that index, using the TS decoder, and prints them
with `formatValue`. A failure reads, for example: "state 18,433: TS reached `[pc |-> …]` from 9,201
by action 3; Rust reached `[pc |-> …]` from 9,201 by action 4". That is two orders of magnitude
more precise than "distinct states: expected 282,251, got 282,250".

It runs on every corpus model that both engines complete, with `-nowarning` and without, since the
assigned shortcut differs between the two. It uses 1 thread and 4 for Rust: the logs must be
identical.

### 6.4 Engine matrix: extend `engine-coverage.ts`

Today it runs `PROVE_IT_ENGINE=debug` against `0`. It becomes a matrix of settings:
- `off` (the interpreter);
- `ts` (`PROVE_IT_ENGINE=debug`, `BACKEND=ts`);
- `rust-1` and `rust-4`.

For each model it records the verdict, the `ModelOutcome` fields (`OUTCOME_FIELDS`), the
`[engine]` line (`classify`), wall and CPU time, and for Rust which tier finished: Rust completed,
declined to the TS engine, or stopped to the interpreter. The gates:
- every setting reaches the same outcome as `off`, as today, for every setting;
- a **coverage regression**: a model the TS engine completes that Rust declines or stops on, other
  than a reason listed in `native/coverage-allowlist.json`. The list shrinks as milestones land and
  must be empty before Rust becomes the default;
- the tally adds a "gained" table of models Rust completes and the TS engine does not, such as wide
  strings, VIEW or symmetry in parallel, and liveness with symmetry later.

`parity.yml`'s `engine-coverage` job runs the matrix on `depot-ubuntu-24.04-16`. The `rust-4`
column runs with `--concurrency 3`, so its threads don't oversubscribe the 16 cores. The job
reports CPU time beside wall time.

Rust reports its own tier on an extra debug line, `[engine] native: declined: <reason>` or
`[engine] native: stopped: <reason>`. `classify` skips `native:` lines the way it already skips
lines ending in ` runs as closures`, and reads the tier from them separately. The TS engine's line
that follows keeps its meaning.

### 6.5 Unit-test parity

- **Behavioural tests run twice.** `engine.test.ts` (`checkInEngine` reads `[engine]` lines),
  `parallel.test.ts`, `check.test.ts`, `liveness.test.ts`, `counter-example.test.ts`, the `tlc-*`
  tests, `cli.test.ts` and the rest call `check()` or the CLI. A second job runs the whole of
  `bun test --parallel` with `PROVE_IT_ENGINE_BACKEND=rust`. For the tests to apply unchanged, Rust
  emits **the same `[engine]` lines** with the same wording (`reportEngine`):
  - `checked N states on T threads in M ms with V values`;
  - `handed over after M ms: <reason>`;
  - `skipped: <reason>`;
  - `found N states in M ms; the interpreter checks the temporal properties`.
- **Tests of TS internals** stay TS-only, because "never weaken a test" rules out skipping them
  silently. Examples are `getMemoStatistics` and `MemoTable` and `EpochCache` in `engine.test.ts`.
  They are listed in `native/ts-only-tests.json` with a Rust counterpart named for each, for
  instance the memo table's probation in `cargo test -p tla-engine memo::probation`.
- **Store and fingerprint tests run against both implementations.** `engine-store.test.ts` and
  `engine-fingerprints.test.ts` import `src/engine/store.ts` and `src/engine/fingerprint.ts`. A
  test-only facade, `src/engine/native-store.ts`, exports the same names (`int`, `str`, `setOf`,
  `except`, `exceptAt`, `recordOf`, `tupleOf`, `getValueCount`, `resetStore`,
  `getStateFingerprints`, …) as thin N-API calls. Per-call cost does not matter in tests. The tests
  then use the `describe.each` over implementations they already have
  (`describe.each(["local", "shared"])`) with `"native"` added. Their assertions, such as "an
  EXCEPT result has the id of the same tuple built directly", hold unchanged.
- **Rust's own tests** (`cargo test`) port the same cases plus property tests: the ordering laws
  of `compare` (antisymmetry and transitivity on generated values), and that `setOf` is invariant
  under permutation of its input.

### 6.6 Store-op replay: new, id-exact

`PROVE_IT_STORE_TRACE=path` makes `store.ts` append each public operation as words: op code,
argument ids or texts, and the result id or bail reason. That covers `int`, `str`, `model`,
`setOf`, `union`, `except`, `exceptAt`, `recordOf`, `functionOf`, `appendTuple`, `compare`,
`isMember` and the rest. `native/tools/replay` re-executes the trace on the Rust store and asserts
that every result id and every bail reason is identical.

This works because the Rust store keeps the TS hashes and allocation order (2.1). The prototype
already shows it on 2M operations. It tests hashing, `compare`, set sorting, EXCEPT patching and
the bail rules in isolation from the compiler, on real corpus traffic. It runs single-threaded
(4.3). If Rust later changes allocation for speed, for example by tagging small integers, the
replay switches to comparing structural canonical forms instead of ids.

### 6.7 Self-checks that run on the corpus

- **Memo off:** `PROVE_IT_MEMO=off` disables every memo and epoch table. The state log must be
  identical.
- **Epoch check:** `PROVE_IT_EPOCH_CHECK=1`, as in TS.
- **Fingerprint verify:** `PROVE_IT_FP_VERIFY=1` (2.3).
- **Symmetry check:** `PROVE_IT_SYMMETRY_CHECK=1` (5.3).
- **Determinism:** Rust with 1, 2, 3, 4, 8 and 16 threads on `depot-ubuntu-24.04-16` must give
  identical state logs and stdout. A debug build feature, `chaos`, inserts random yields at
  shard-lock and barrier points. It runs nightly. The `FpSet` and the store shards also get `loom`
  model tests.
- **Unsafe code:** `cargo miri test` on `tla-values` (the arena, the table, the store), and
  `cargo fuzz` on random store operation sequences, nightly for one CPU-hour.

### 6.8 Value and enumeration oracle against TLC itself

A small Java program, `native/oracle/ValueOracle.java`, compiled against the pinned
`tla2tools.jar` (Depot already builds it in `benchmark.yml`), reads JSON lines of operations:
- build values with TLC's own classes (`IntValue.gen`, `StringValue`, `ModelValue.make`,
  `SetEnumValue` + `normalize()`, `RecordValue`, `FcnRcdValue`, `TupleValue`, `SetOfFcnsValue`,
  `SubsetValue`, `UnionValue`, …);
- intern a list of strings first with `UniqueString.uniqueStringOf`, in a given order, to fix TLC's
  string ranks. This mirrors `setStringOrder`;
- answer `compareTo`, `equals`, `member`, `fingerPrint(FP64.New())` with `FP64.Init(0)`,
  `toString`, the enumeration order of lazy sets through their `elements()` enumerators, and
  whether and how each throws, as the exception class and message.

`scripts/value-oracle.ts` generates seeded batches and runs them through the oracle, through the
TS interpreter (`values.ts`, `tlc/fingerprint.ts`), and through the Rust store (N-API test hooks).
It reports any disagreement, shrunk to a minimal value pair. The generator targets the known traps:
- ranked against unranked strings, and strings created at run time;
- untyped and typed model values (`A_x`) mixed with other kinds;
- records against string-domain functions, tuples against `1..n` functions, the empty function;
- `-2^31`, `2^31-1`, and arithmetic that overflows;
- sets of sets in TLC order;
- `UNION` with overlapping members (duplicates when streamed);
- `SUBSET` and `[S -> T]` order;
- characters above `0xFF` (wide strings).

It runs nightly on Depot with live TLC. Regressions are frozen into
`tests/conformance/value-oracle/*.jsonl` and replayed on every PR without Java, against the
recorded answers.

**Fingerprint conformance.** `conformance:fingerprint` (`scripts/fingerprint-conformance.ts`)
today checks the *prover's* obligation fingerprints against tlapm's proof reuse
(`src/prover/prep/fingerprint`). It does not check TLC's FP64. Keep it for the prover and add
`conformance:fp64` (`scripts/fp64-conformance.ts`), which compares three things:
- the oracle's `fingerPrint` for generated values;
- the state-log fingerprints of the TS engine, the Rust engine, and the interpreter's
  `getTlcFingerprints`, on every engine-completed corpus model, through `PROVE_IT_FINGERPRINT=check`
  semantics;
- TLC's collision line from 6.1.

### 6.9 Generated specs against TLC

`scripts/fuzz-specs.ts` writes small specs whose *outcome depends on order and value semantics*:
- `\E e \in S : x' = f(e)` with an invariant that fails at a chosen element. Which state TLC
  reports first, its trace, and the counts at the violation all depend on enumeration order;
- `x' \in S` over lazy sets;
- CHOOSE over sets in TLC order;
- conjunct orders that exercise the assignment rule, with `-nowarning` and without;
- EXCEPT chains;
- comparison errors on the evaluated path versus a short-circuited one;
- constraints that fail on states that violate invariants;
- deadlock;
- VIEW and SYMMETRY.

Each spec runs through TLC, the TS checker and Rust, and 6.2's normaliser compares the outputs.
Depot runs 2,000 seeds a night on `depot-ubuntu-24.04-16`. A failing case is shrunk by deleting
conjuncts and simplifying expressions, then committed to `tests/fixtures/fuzz/` with TLC's output.

### 6.10 Front end (stage 4)

The stage-4 front end has three checks:
- **IR byte-equality:** the TS lowering and the Rust front end produce identical IR for all 823
  corpus models and the 1,873 SANY modules;
- **SANY messages:** `conformance:sany` (`scripts/proof-conformance.ts` against `sany.json`) gains
  `--backend rust`;
- **the fallback decision:** the native front door must fall back to JS on every module where SANY
  prints anything beyond the standard progress lines. A test asserts this on the SANY corpus.

### 6.11 Forced hand-over

`PROVE_IT_STOP_AT=k` makes either engine stop with a synthetic unsupported reason before expanding
state k. For every corpus model with a violation or deadlock, and for random k on the rest, the
interpreter's continuation must print **byte-identical** output to the run without the stop. This
tests the checkpoint encoding, the decoder, `resumeFromEngine`, and the progress-reporting flags
(`engineReport.isReported`) under every interleaving. The TS engine gets the same flag first
(M0), so the test exists before Rust does.

### 6.12 CI gates and machine sizes

| Workflow | Machine | When | Runs | Gate |
|---|---|---|---|---|
| `verification.yml` | `depot-ubuntu-24.04` | every PR | build (now with `cargo build --release`), typecheck, lint, `cargo clippy -D warnings`, `cargo test`, `bun test` with `BACKEND=ts` and `BACKEND=rust`, differential smoke (40 models ≤ 2 s TLC, cached TLC stdout), store-op replay (10 models), value-oracle regressions | all green |
| `parity.yml` | `depot-ubuntu-24.04-16` | push to main, manual | conformance `--check` for both backends, `--compare-backends`; engine matrix; differential on every model ≤ 20 s TLC (default and `-tool`); state-log diff on every engine-completed model; forced hand-over; self-checks | zero new differences; no coverage regression |
| `parity-nightly.yml` (new) | `depot-ubuntu-24.04-16` | nightly | value oracle (live TLC), spec fuzz (2,000 seeds), determinism 1–16 threads with `chaos`, cargo fuzz, Miri | zero disagreements |
| `benchmark.yml` | `depot-ubuntu-24.04-4` | weekly, manual | adds `prove-it-rust`, `prove-it-rust-aot`, `prove-it-rust-4` | verdicts agree (as today) |
| `compare.yml` | `depot-ubuntu-24.04-4` | manual on a branch | base vs head, both backends | no model slower by more than 5%, or 3 ms on models under 0.1 s |
| `release.yml` | per platform (7.3) | version bump | build addons, smoke the differential on 20 models per platform | all platforms or none |

Timings are gated only on `-4` machines, so every number is comparable with the recorded Depot
runs. Parity runs on `-16`.

---

## 7. Distribution

### 7.1 npm

- The main package `@atemp/prove-it` stays pure JavaScript and always works without the addon,
  since the TS engine remains.
- Per-platform packages with no JavaScript and no install scripts carry `prove-it-engine.node`
  only:
  - `@atemp/prove-it-linux-x64-gnu`, `-linux-arm64-gnu`, `-linux-x64-musl`, `-linux-arm64-musl`;
  - `@atemp/prove-it-darwin-arm64`, `-darwin-x64`;
  - `@atemp/prove-it-win32-x64-msvc`.

  Each has `os`, `cpu` and `libc` fields and the same version as the main package. The main
  package lists them as `optionalDependencies`. This is the esbuild and SWC model: npm, pnpm, Yarn
  and Bun install only the matching one, without scripts, so it works with the
  `--ignore-scripts` that `release.yml` and the CI use.

  The library keeps **no runtime dependencies in the JS sense**: nothing is imported, and a missing
  addon falls back. If the maintainers read "no runtime dependencies" to exclude optional
  dependencies too, the fallback design is to vendor all addons in `dist/native/<triple>/`. That
  costs roughly 15–25 MB unpacked for seven platforms, to be measured once the addon exists.
- **Loader:** `src/engine/native.ts` resolves the platform package with `import.meta.resolve`, or
  falls back to `dist/native/<triple>/`, and loads it with `process.dlopen`. *Measured:* 0.2–0.3 ms
  warm in Bun and Node, against 0.5–0.75 ms through `createRequire`. The very first cold load was
  146 ms, which was the page cache. The loader checks `abiVersion()` against `IR_VERSION`. On any
  failure, and with `PROVE_IT_ENGINE_BACKEND=ts`, it uses the TS engine and reports the reason on
  the `[engine]` debug line. `auto` becomes the default only after stage 1's gates.
- **ABI:** Node-API version 8 is stable across Node ≥ 12.22 and Bun. There is no node-gyp and no
  per-Node-version build. The binding is hand-written, as in the prototype `proto/napi-cost`: about
  a dozen `napi_*` calls for a dozen exported functions, which avoids proc-macro dependencies.
  napi-rs is a fine alternative if the surface grows, since it is a build-time dependency only.

### 7.2 The crate

```
packages/prove-it/native/           Cargo workspace; rust-toolchain.toml pins 1.99.1 (scripts/ci/bootstrap.sh rust)
  crates/tla-values      store, compare, FP64, arena, transfer encoding           (no dependencies)
  crates/tla-engine      IR decoder, compiler, memo, walker, search, parallel, symmetry, graph, live tables
  crates/tla-live        stage 3: tableau, SCCs, counterexamples
  crates/tla-front       stage 4: lexer, parser, resolver, levels, SANY success path, config, TLC order
  crates/prove-it-napi   cdylib: the N-API binding
  crates/prove-it-cli    stage 4: the native front door
  oracle/ValueOracle.java, tools/replay, fuzz/
```
`Cargo.lock` is committed and builds use `--locked`, with no network in `build.rs`. Release
profile: `lto = "fat"`, `codegen-units = 1`, `panic = "unwind"` so `catch_unwind` works at the
boundary. CPU baseline is `x86-64-v2` (no AVX2 assumption) and the default for arm64.

### 7.3 Standalone binaries

- **Stages 1–3:** `scripts/build-binary.ts` embeds the addon in the Bun executable as it embeds the
  SANY snapshot (`assets`), extracting it at first use. If Bun's compiled executables cannot load an
  embedded `.node` (to check in M1), the release archive puts `prove-it-engine.node` beside the
  binary instead. `build-binary.ts`'s post-build checks gain a case with
  `PROVE_IT_ENGINE_BACKEND=rust` expecting ` on 1 thread ` and the Rust tier in the `[engine]`
  line.
- **The AOT binary becomes the default.** It is 1.4–2× slower than the JIT binary on large models
  only because it cannot run generated code. With the Rust engine it does not need to: Init, Next
  and invariants run natively. Its 16 ms start (against 36 ms) then comes free for small models. M7
  measures this; it depends on Bun's AOT compiler loading N-API addons.
- **Stage 4:** the release archive holds `prove-it` (native, the front door) and `prove-it-js` (the
  Bun binary). The native binary runs the common path itself and `exec`s `prove-it-js` on a
  fallback (8.4). It is a single file in stage 5.
- **Platforms and CI:** Linux builds and smoke tests run on Depot (`depot-ubuntu-24.04`, plus an
  arm64 runner). macOS and Windows build and run the 20-model differential smoke on hosted runners
  of those systems. A platform that cannot be tested is not published, and its users get the TS
  engine.

---

## 8. Expected performance

### 8.1 Model and assumptions

`native/prototypes/estimate.ts` projects each model from today's Depot times
(`dash/r3/suite.json`). It uses these assumptions:
- **Fixed cost F.** Process start, parse, SANY and environment take `min(40 ms, 80% of the run)`
  in stages 1–3: 36 ms for the bytecode binary on a one-state spec, plus parsing. In stage 4 F is
  6 ms: native start is 1.45 ms *measured*, then parsing and analysis at native speed.
- **Stage 1, single thread.** The search speeds up by `k1`. The middle case is 1.6×, the range
  1.3–2.0×. The measurements behind it: interning 1.7×, probes 1.7× (plus the 4–10% post-search
  fingerprint pass removed), invariants and constraints about 2× from fused closures against TS's
  *best* case (more against the megamorphic real one), and generated Init/Next JS about 1–1.5×,
  because JSC already runs it as straight-line code. Plus 2 ms for building the IR, loading the
  addon and compiling.
- **Stage 2.** Searches longer than 0.5 s gain 2.5× on 4 cores; under 0.1 s, nothing; linear in
  between.
- **Stage 3.** Liveness checking costs about what the engine's search costs (the headroom page's
  assumption), at Rust speed.

### 8.2 Projection (k1 = 1.6), seconds on `depot-ubuntu-24.04-4`

| Model | TLC 1w | TLC 4w | tla-ts | Prove It today | Stage 1 | Stage 2 | Stage 3 | Stage 4 | What drives it |
|---|---|---|---|---|---|---|---|---|---|
| commit | 3.99 | 1.97 | 3.13 | 0.28 | 0.19 | 0.17 | 0.17 | 0.13 | store, probe; levels too short to parallelise much |
| philosophers | 1.21 | 0.93 | 0.98 | 0.15 | 0.11 | 0.11 | 0.11 | 0.08 | store |
| queue | 0.47 | 0.48 | 0.24 | 0.06 | 0.05 | 0.05 | 0.05 | 0.02 | startup |
| MCbtree | 20.9 | 6.96 | 6.48 | 0.69 | 0.45 | 0.23 | 0.23 | 0.20 | invariants, threads |
| SimpleRegular | 2.90 | 1.73 | 2.32 | 0.55 | 0.36 | 0.22 | 0.22 | 0.18 | threads |
| SyncCons | 0.46 | 0.45 | 0.21 | 0.06 | 0.05 | 0.05 | 0.05 | 0.02 | startup |
| 2PCwithBTM | 0.35 | 0.36 | 0.15 | 0.05 | 0.05 | 0.05 | 0.05 | 0.01 | startup |
| VoucherRedeem | 0.52 | 0.48 | 0.25 | 0.07 | 0.06 | 0.06 | 0.06 | 0.03 | startup |
| test19 | 0.61 | 0.59 | 0.46 | 0.09 | 0.07 | 0.07 | 0.07 | 0.04 | probe |
| MCBakery | 5.61 | 4.16 | 6.80 | 1.04 | 0.67 | 0.29 | 0.29 | 0.26 | invariants, threads |
| MCLamportMutex | 9.15 | 4.65 | 11.37 | 2.13 | 1.35 | 0.57 | 0.57 | 0.53 | invariants and memo, threads |
| MCSingleNode | 3.25 | 1.76 | 2.42 | 0.77 | 0.50 | 0.24 | 0.24 | 0.20 | invariants, threads |
| MCDisruptor_MPMC | 2.43 | 1.22 | 2.10 | 0.26 | 0.18 | 0.16 | 0.16 | 0.13 | store |
| Paxos_MC | 5.67 | 2.30 | 4.33 | 1.37 | 0.87 | 0.37 | 0.37 | 0.34 | symmetry loop, threads |
| ReadersWriters | 1.50 | 1.18 | 0.86 | 0.38 | 0.36 | 0.36 | 0.10 | 0.07 | liveness on the graph |
| TokenRing | 1.26 | 1.01 | 0.95 | 0.54 | 0.51 | 0.51 | 0.16 | 0.13 | liveness on the graph |
| ACP_SB_TLC | 0.85 | 0.73 | 0.53 | 0.12 | 0.09 | 0.09 | 0.09 | 0.06 | startup, store |
| Chameneos | 0.77 | 0.74 | 0.51 | 0.13 | 0.10 | 0.10 | 0.10 | 0.06 | startup, store |

| Geomean over 18 | Today | Stage 1 | Stage 2 | Stage 3 | Stage 4 |
|---|---|---|---|---|---|
| seconds (k1 = 1.6) | 0.263 | 0.200 | 0.154 | 0.135 | 0.084 |
| vs TLC, 1 worker (k1 = 1.3 / 1.6 / 2.0) | 6.6× | 7.7 / 8.7 / 9.8× | 10.3 / 11.3 / 12.3× | 11.6 / 12.9 / 14.3× | 17.6 / 20.5 / 24.1× |
| vs tla-ts | 4.4× | 5.1 / 5.8 / 6.6× | 6.9 / 7.6 / 8.3× | 7.8 / 8.6 / 9.6× | 11.8 / 13.8 / 16.2× |

### 8.3 Reading the projection

- These figures are lower than the headroom page's "Rust core, 20–30× vs tla-ts". That page
  assumed Rust's constant factor was larger. The prototypes say it is about 1.7–2× on the same
  algorithm. The rest has to come from threads, which stage 2 brings, and from startup, which
  stage 4 brings. A Cranelift tier (3.1) is the main upside: invariant-heavy models
  (LamportMutex, Bakery, SingleNode, btree) could move toward `k1 ≈ 3` on their invariant share.
- **Stage 1 does not slow small models.** Its overhead is IR, load and compile, budgeted at 2 ms
  and gated in M7. If shipping the AOT binary as default works out (7.3), small models gain
  about 20 ms in stage 1 already. The table leaves that out.
- **CPU time** falls more than wall time. Today a short run spends 1.7–2.6× its wall time on JIT
  threads and GC, and in stages 1–3 the engine part of that disappears. `bench-suite.ts` already
  records CPU time, and `compare.yml` reports it.
- **Stage 3 gains are algorithmic** (no replay, no object graph). They would be about the same in
  TS, and Rust adds only its constant factor on top. Its order relative to stage 2 can swap if
  liveness models matter more to users.

### 8.4 Stage 4's process model

The native binary parses the arguments, the config and the modules, runs the IR through the
engine, and **buffers stdout** until the run completes or the first Progress line is due. At that
point long runs no longer care about 36 ms. It falls back to `prove-it-js` with the same argv
(`exec`), having printed nothing, on any of these:
- an option outside its supported set;
- a parse or SANY condition other than the success path;
- an assumption to evaluate that it can't;
- a decline.

On a stop after output has been flushed, it writes a checkpoint file and runs
`prove-it-js --resume <file>`. That is an internal option: `check.ts` resumes from the checkpoint
and the CLI suppresses the lines already printed, tracked as message codes in the file. The
differential (6.2) covers both paths, and 6.11's forced hand-over runs through the native binary
too.

---

## 9. Risks to parity and what catches each

| Risk | Example | Caught by |
|---|---|---|
| TLC order of composite values diverges | `compareFunctions` on records vs functions; set of sets sorted differently | store-op replay (6.6), value oracle (6.8), state-log diff (6.3) |
| String ranks | a string created at run time; an unranked text compared by text; the TLC string order list built differently | value oracle with `UniqueString` order; IR golden tests of the text table (M3); state log |
| Model values | typed `A_x` mixed with untyped, compared or tested for membership | value oracle; `bail` parity in store-op replay |
| Integer semantics | overflow at ±2^31; `\div` and `%` with negatives; `^` | spec fuzz (6.9), value oracle |
| Lazy-set enumeration order | SUBSET, `[S -> T]`, UNION streaming duplicates, `x' \in` lazy | enumeration oracle (6.8), state log, compile-time decline until each lands |
| Action walk semantics | first-assignment rule, UNCHANGED, assigned shortcut with warnings on vs off, `\E` bound order, `isPastWalk` | state log with and without `-nowarning`; TLC's own test models in the corpus (`tlc/test-model`); differential |
| Missing bail (wrong success) | Rust doesn't stop on a comparison TLC fails | conformance status (6.1), engine matrix against `off` (6.4), fuzz with error triggers |
| Extra bail (slower, not wrong) | Rust stops where TLC doesn't | coverage regression gate (6.4) |
| Memo staleness | epoch reused; footprint misses a slot | memo-off and epoch-check runs (6.7); footprint unit tests |
| Parallel nondeterminism | a race in the FpSet; a candidate key lost | 1–16 thread state logs on `-16` plus `chaos`, `loom` (6.7) |
| Stopping at the wrong place in parallel | a stop at a later parent wins | forced stops at random k with 4 threads (6.11), conformance of violation counts |
| Fingerprint semantics | FP dedup vs exact dedup on a real collision; wide strings | FP verify (2.3), fp64 conformance (6.8), wide-string corpus models compared against TLC |
| Trace printing | record vs function representation | stays in the interpreter (2.8); differential stdout |
| Checkpoint encoding and resume | a string with surrogates; records tagged as functions; the progress flags | forced hand-over (6.11), round-trip tests of `transfer.ts` encoding from Rust |
| Output format | `-tool` codes, message order, `Finished computing initial states` printed twice | differential in both modes (6.2) |
| Normalisation hides a difference | a regex eats counts | normaliser unit test with mutated TLC output (6.2) |
| Two implementations drift | a TS engine fix not mirrored in Rust | every PR touching `src/engine` or `native/` runs both backends; `--compare-backends` |
| Undefined behaviour or panic | an arena bug | Miri, cargo fuzz, `catch_unwind` with a CI-fatal `[engine]` line (3.4, 6.7) |
| Deep recursion | a recursive operator 10^5 deep | the depth counter stops; corpus models with deep recursion in the matrix |
| Platform differences | musl allocator speed; Windows virtual memory reservation | per-platform release smoke differential (6.12) |
| TLC changes under us | the pinned `TLC_COMMIT` moves | re-record outcomes and stdout on every pin change; the known-differences file must be updated in the same PR |

---

## 10. What was measured

All under `native/prototypes/`.

### 10.1 N-API crossing cost (`napi-cost/`)

A dependency-free Rust `cdylib` that declares the `napi_*` functions itself, with a Bun and Node
driver in `bench.ts`:

| Call | Bun 1.4.4 | Node 22.23.4 |
|---|---|---|
| `noop()` | 94–112 ns | 15 ns |
| `add(i, 1)` | 123–143 ns | 27 ns |
| `sum(Int32Array(16))`, zero-copy | 158–182 ns | 64 ns |
| `sum(Int32Array(1024))`, zero-copy | 162–192 ns | 120 ns |
| Rust → JS callback | 35–47 ns | 59 ns |
| `bun:ffi` `add` / `sum(ptr)` | 10 ns / 75 ns | — |
| load (`process.dlopen`, warm) | 0.26–0.32 ms | 0.20–0.29 ms |

Consequence: one call per check, bulk liveness tables, no per-state crossing (1.2, 5.1).

### 10.2 Hash-consed store and state table (`store-bench/`, `workload.ts`)

`workload.ts` imports the repository's `src/engine/store.ts` read-only. `src/store.rs` ports its
layout, hashes and allocation order. Each of 2M steps does:
- an EXCEPT on a 5-key function;
- a 2-field `recordOf`;
- a `withElement` on a growing set;
- a 3-element `setOf` (sorted and deduplicated);
- an append or reset of a short tuple;
- a probe of a 4-id state.

Both find **37,986 values and 317,584 distinct states with checksum −1720536883**, so the ids are
identical.

| ns per step | TS (Bun) | TS (Node) | Rust |
|---|---|---|---|
| store operations only | 274–311 | — | 159–174 |
| plus [hash, index] state table | 449–473 | 557–628 | 260–312 |
| plus FP64-keyed set, every state fingerprinted | — | — | 298–329 |

### 10.3 FP64 (`store-bench/src/fp.rs`, `fp-check.ts`)

`u64` FP64 equals `getTlcFingerprint` on a mixed sample (−2179341659381351120) and on a million
5-integer states (xor 8882444436892305134). Rust takes 15.5 ns per state; the TS interpreter's path
takes 317 ns.

### 10.4 Evaluating an invariant (`store-bench/src/eval.rs`, `eval.ts`)

The figures are in the table in 3.1. The TS figure is a single monomorphic closure tree, so it is
the JIT's best case.

### 10.5 Start-up and IR size

- Process start: Rust "hello" 1.45 ms, `bun -e 1` 5.3 ms, `node -e 1` 23.5 ms, median of 30.
- Whole-module AST as JSON (`ir/ast-size.ts`): Commit 38 KiB in 0.6 ms, 2PCwithBTM 82 KiB in
  1.2 ms, LamportMutex 88 KiB in 2.9 ms, btree 221 KiB in 3.8 ms (cold).

### 10.6 Not measured

These are estimates and would need measuring:
- the Rust walker against JSC running `codegen.ts`'s generated code on real Init/Next;
- real megamorphic TS invariants;
- Cranelift compile latency and size;
- Bun AOT loading N-API addons;
- the 4-core scaling.

Stage 1's milestones measure the first and fourth. Stage 2 measures the last.

---

## 11. Stage 1, broken into milestones

Stage 1 ships when M7's gates pass. Each milestone merges on its own, with the Rust backend off by
default until M7.

### M0. The harness first, in TypeScript only

The harness has to exist before any Rust does, so that M1–M7 are measured against a fixed
baseline.

**Work:**
- `scripts/normalize-output.ts`, extracted from `tests/unit/cli.test.ts`;
- `scripts/differential.ts`;
- `record-tlc.ts --stdout` with the cache;
- `tests/conformance/known-differences.json` from a full run;
- `PROVE_IT_STATE_LOG` in `search.ts` and `scripts/state-log-diff.ts`;
- `PROVE_IT_STORE_TRACE` in `store.ts`;
- `PROVE_IT_STOP_AT` in `search.ts`;
- `--backend`/`--compare-backends` plumbing in `check-model.ts`, `conformance.ts` and
  `engine-coverage.ts`, accepting only `ts` for now;
- the fingerprint field in `compare-outcome.ts`.

**Acceptance:**
- differential on every model ≤ 20 s TLC: TS engine vs interpreter has no differences beyond those
  listed, and TLC vs Prove It matches `known-differences.json`;
- `PROVE_IT_STOP_AT` at random k on every violating corpus model gives byte-identical output;
- the state log of the TS engine with 1 and 4 workers is identical on the models the parallel
  search takes;
- the normaliser unit test passes with mutated counts surviving;
- `bun run test` is unchanged.

#### M0 as built

Where the code made this design change, the code wins, and this records how:

- **Recordings (6.2).** TLC's outputs are committed in `tests/conformance/tlc-stdout/`, one JSON
  file per model and mode (exit code, stdout, stderr), not kept as a CI artifact. All 1,466 runs of
  the 733 models under 20 s take 8.7 MB, so PR runs need neither a JVM nor a download. The file name
  is a hash of `TLC_COMMIT`, the mode, the model id, every file in the model's directory, and the
  commits of the `tlapm` and `community` corpora that hold the library modules
  (`scripts/tlc-recordings.ts`). `TLC_COMMIT` lives there, and `record-tlc.ts --stdout` refuses to
  record unless the environment's `TLC_COMMIT` names it, since a jar built without its git history
  can't say which commit it is. `.depot/workflows/record-tlc.yml` records what is missing on Depot,
  by hand, and keeps the recordings as its artifact to commit.
- **What the differential runs (6.2).** It runs `dist/cli.js` with TLC's own command line
  (`-DTLA-Library=… tlc2.TLC -workers 1 -nowarning -seed 4 -fp 0 -lncheck final
  -noGenerateSpecTE [-tool] -metadir … -config …`), not a compiled binary, under whichever runtime
  runs the script. The pairs it compares are `tlc/ts`, `ts/interpreter` and, with `--stop-at`,
  `ts/stopped` (6.11). Each entry of `known-differences.json` is keyed by model, mode and pair, and
  holds the diff as the lines one side drops (`-`) and the other adds (`+`), without positions.
  An entry whose difference is gone is reported, not failed; `--update` rewrites the file and
  keeps the reasons.
- **Normalisation (6.2).** Besides the list above, the normaliser:
  - drops what TLC appends to a `Parsing file` line about where it found the module, the jar of a
    standard module or the library-path link of a library module, which Prove It doesn't print;
  - reduces every other path in those lines to its file name, as recordings are made in another
    directory;
  - drops `-tool`'s whole progress message (code 2200), not only its `Progress(…)` line;
  - and drops Prove It's `[engine]` lines from stderr.
- **The fingerprint field (6.1).** TLC prints a probability, not a distance, so the field is
  `fingerprintProbability`: the text after "based on the actual fingerprints:  val =". TLC prints
  that line only when the optimistic estimate is at least 1E-10 (`ModelChecker.reportSuccess`), so
  14 of the 449 successful models under 20 s have it. `record-tlc.ts --stdout` adds it to
  `expected.json` from the default-mode recordings whose counts agree with it, rather than
  re-recording every outcome.
- **The backend (6.1).** `check-model.ts` checks in-process, so it can't read its own `[engine]`
  lines. The runners read them from its stderr (`scripts/engine-runs.ts`), and `conformance.ts`
  keeps each verdict's backend and `[engine]` line in `.results.json`. `--threads` is left for
  M1. `engine-coverage.ts` keeps each run under `runs`, keyed `off` and by backend, instead of
  `on` and `off`.
- **The state log (6.3).** The TS engine writes it once the search completes or stops, as JSON
  lines: a header (`version`, `variables`, `count`, `stopped`, `expanding`), then per state
  `[index, parent, action, fingerprint, words, strings]`. The state itself is in `transfer.ts`'s
  encoding, which Rust can write too (5.2), so `state-log-diff.ts` prints both states and their
  parents without running the model again. Two logs agree when their headers' variables and the
  first four fields of every state do. The TS engine knows a state's action only when it labels
  its steps for ENABLED (`isLabelled` in `check.ts`); otherwise the action is `-1`. The optional
  per-expansion counts are left out: a level the workers expand reports only its totals to the
  coordinator.
- **The store trace (6.6).** One JSON line per operation, `[name, arguments, result]`, with
  `{"bail": reason}` for a stop, rather than words. An operation another calls is not written. A
  reset records TLC's string order then, which ranks the strings the store makes. The operations
  are exported with `let` and replaced by tracing wrappers only when the setting names a file, so
  the code that runs without it is the code that ran before. Only the main thread writes, so a
  trace is of a search on one thread (the default). `scripts/store-replay.ts` replays a trace on
  the TS store, as the reference for `native/tools/replay`.
- **Forced hand-over (6.11).** With `PROVE_IT_STOP_AT` the TS search stays on one thread, since
  a level the workers expand has no single state to stop before. `differential.ts --stop-at`
  picks the state from those the engine's run found, by a hash of the model's id, and only for
  models the engine searched.
- **Cost when off.** On `benchmarks/commit`, six interleaved runs each of `main` and this branch:
  the engine's time is 474–545 ms on this branch and 481–730 ms on `main` under Bun (median about
  500 ms both), and 594–722 ms and 572–660 ms under Node (median about 628 ms both).

#### M0 acceptance, as run

On a 4-core machine, against the 733 models with TLC under 20 s:
- **Differential.** The 1,466 runs (default and `-tool`) leave 62 listed differences, each with
  its reason in `known-differences.json`: 56 between TLC and the TS engine, 6 between the TS
  engine and the interpreter, and none between the engine and the engine stopped part way.
  - 18 of the 56 are TLC at `TLC_COMMIT` rejecting precedence conflicts in SANY (on 7 models)
    that the TLC behind `expected.json` accepted, so those outcomes in `expected.json` are not
    TLC_COMMIT's.
  - The 6 engine/interpreter differences are engine bugs in the initial-state messages.
  - The rest are Prove It printing records' fields in another order in traces, error messages
    worded otherwise, a step named `Next` where TLC names its action, a POSTCONDITION reported
    false, and a crash in `getSpanLocation` on `test52`; and two that depend on TLC's runtime: a
    Java stack overflow and the install path in `TLCGet("config")`.
- **Forced hand-over.** `differential.ts --stop-at` stopped the engine on 547 models in both modes,
  the violating ones among them, with identical output each time.
- **State logs.** `engine-coverage.ts --state-logs` compared the logs on 1 and 4 threads on the
  245 models the engine completes. They are identical on all 245, but the workers took levels on
  only 2 (`ccf/tla/consistency/MCSingleNode`, `TeachingConcurrency/SimpleRegular`); the rest are
  too small or use symmetry or a VIEW. `benchmarks/commit` is the test that does take them.
- **Normaliser, unit tests, conformance.** The normaliser's test passes with mutated counts
  surviving; `bun test tests/unit` passes (2,905 tests); `conformance --check` matches all 772
  models of `passing.json`; the engine on and off reach the same outcome on every model.

### M1. Crate, binding, loader, packaging

**Work:**
- `packages/prove-it/native/` workspace pinned to 1.99.1;
- `prove-it-napi` exporting `abiVersion()` and a `check()` that always declines;
- `src/engine/native.ts` with `process.dlopen` and the fallbacks;
- `PROVE_IT_ENGINE_BACKEND`;
- the platform package layout and `scripts/dist.ts` support;
- `build-binary.ts` embedding the addon;
- the cargo jobs in `verification.yml`.

**Acceptance:**
- `bun run test` passes with `BACKEND=rust`, because everything declines to the TS engine: each
  run shows `[engine] native: declined: …` and then the TS engine's usual line;
- addon load under 1 ms warm in Bun and Node on Depot;
- the bytecode and AOT binaries both load the addon, or the beside-the-binary fallback is chosen
  and documented;
- a package without the platform addon installs with `--ignore-scripts` and runs on the TS
  engine;
- `release.yml` dry-run packs all packages.

### M2. Values and fingerprints (`tla-values`)

**Work:**
- the store per 2.1: every exported function of `store.ts` except shared mode, which is stage 2;
- `compare`/`equals`/`isMember` with every bail;
- FP64 per 2.4, with the per-value F and |v| and the linear state fingerprint;
- the transfer encoding writer;
- the N-API test hooks;
- `src/engine/native-store.ts`.

**Acceptance:**
- **store-op replay id-exact** on the traces of every corpus model the TS engine completes;
- `engine-store.test.ts` and `engine-fingerprints.test.ts` pass with the `"native"`
  implementation added;
- `conformance:fp64`: Rust fingerprints equal the TS engine's for every state of every
  engine-completed model, and equal the oracle on 100k generated values;
- value oracle (6.8) with zero disagreements on 100k operations;
- `cargo miri test` and one CPU-hour of `cargo fuzz` clean;
- workload benchmark within 10% of the prototype (≤ 175 ns per step on store operations).

### M3. The Engine IR

**Work:**
- `src/engine/ir.ts` lowering per 1.3;
- `IR_VERSION`;
- the Rust decoder and an encoder for round-trips;
- golden IR files for 30 representative models;
- `PROVE_IT_IR_DUMP`.

**Acceptance:**
- IR is produced for all 823 corpus models, or a decline names the reason (for example a property
  in an instance, as `toEngineProperties`);
- decode then re-encode is byte-identical for all of them;
- golden files match;
- IR build time ≤ 1 ms median on 2PCwithBTM and ≤ 3 ms on btree on Depot `-4`;
- the string table equals `createTlcOrder`'s order, checked against `getStringRank` for every
  text.

### M4. The expression compiler

**Work:**
- every expression kind and builtin in 3.1, except lazy enumerators and bridged builtins, which
  decline;
- footprints, `cached`, memo and epoch tables per 3.2;
- the fused nodes;
- the bail table per 3.4;
- `PROVE_IT_MEMO=off` and `PROVE_IT_EPOCH_CHECK`.

**Acceptance:**
- **expression differential:** for every compiled invariant, constraint, action constraint and
  property in the corpus, evaluated on the first 1,000 states of the TS engine's state log (decoded
  into both stores), Rust and TS give equal values (by fingerprint) or the same bail reason;
- memo-off results are identical;
- epoch check clean;
- the micro-benchmark of 3.1 at ≤ 800 ns per evaluation for fused nodes.

### M5. Walker, search, checkpoints, single thread

**Work:**
- the Init/Next walker per 3.5, including ENABLED, `isPastWalk`, labelled action steps
  (`spec.actions`) and `PROVE_IT_LIVE_CHECK` parity;
- `runEngine`'s loop per 3.5 with the `FpSet` (2.3), `StateLog`, deadlock, VIEW, symmetry (5.3),
  graph recording and live tables (5.1);
- checkpoints in transfer encoding (5.2);
- callbacks;
- `[engine]` lines with TS wording;
- `PROVE_IT_STATE_LOG` and `PROVE_IT_STOP_AT` in Rust.

**Acceptance:**
- **state logs identical** to the TS engine's on every model both complete, with `-nowarning` and
  without;
- `conformance --check --backend rust` keeps every model in `passing.json`;
- `--compare-backends` shows no difference;
- the **engine matrix** gives identical outcomes for `off`, `ts` and `rust-1`, and every coverage
  regression is in the allowlist with a milestone named;
- **differential:** TS engine vs Rust byte-identical on every model ≤ 20 s TLC, in default and
  `-tool` modes;
- forced hand-over at random k byte-identical;
- the liveness models (ReadersWriters, TokenRing, the corpus's `PROPERTY` models) are identical,
  with the interpreter asking at most one crossing per distinct predicate (counted);
- `bun test` with `BACKEND=rust` is fully green, except tests in `ts-only-tests.json`, each with a
  passing Rust counterpart;
- `PROVE_IT_FP_VERIFY` reports zero collisions on the corpus.

### M6. Lazy sets and pure builtins

**Work:**
- the enumerators of 3.3: SUBSET, `[S -> T]`, record sets, products, UNION streaming, lazy set
  operations, and filters and maps over them;
- SubSeq, SelectSeq, SortSeq, Permutations, IsFiniteSet, the Bags operators.

**Acceptance:**
- **enumeration oracle:** 100k generated small sets give identical order in Rust,
  `getStreamedElements`/`getQuantifierElements`, and TLC's enumerators (nightly with live TLC,
  frozen cases on PR);
- the builtins agree with the interpreter on generated inputs, including bails;
- the coverage allowlist from M5 is **empty**: Rust completes every model the TS engine completes;
- all of M5's acceptance tests still pass.

### M7. Performance and default on

**Work:**
- profiling and tuning on the 18 suite models: incremental fingerprints, memo key packing, fused
  node selection;
- `bench-suite.ts` checkers `prove-it-rust` and `prove-it-rust-aot`;
- `compare.yml` with both backends;
- `PROVE_IT_ENGINE_BACKEND=auto` as the default;
- a release with linux-x64-gnu, linux-arm64-gnu and darwin-arm64 addons (others fall back);
- the AOT binary decision (7.3).

**Acceptance** (on Depot `depot-ubuntu-24.04-4`, `benchmark.yml` with `--runs 5`):
- every checker's verdict agrees with TLC;
- the 8 engine models over 0.25 s are each ≥ 1.3× faster than today's Prove It;
- the suite geomean is ≥ 1.2× faster;
- **no model slower by more than 3%, or 2 ms on models under 0.1 s**;
- CPU time is lower on every engine model;
- `prove-it-rust-aot` is within 10% of `prove-it-rust` on the large models (decides 7.3);
- the full parity workflow (6.12) is green on main for a week of pushes and the nightly jobs are
  green for seven consecutive nights before `auto` ships in a release.
