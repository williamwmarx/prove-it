# A native backend of our own (DESIGN.md 3.1's later tier)

Status: design only (this file, rather than a section of DESIGN.md, so it doesn't conflict with other workstreams' notes), for review before any code. The workspace stays std only: no Cranelift, LLVM,
`dynasm`, `memmap2` or `libc` crate. Everything below is code we write and own.

## 1. Why, and what it replaces

After #45, #53, #60, #73 and #75 the closures are close to what tuning can reach. Rust beats
the TypeScript engine 1.30× on the suite's geomean in wall time, but not by 1.3× on Commit,
btree, SimpleRegular, MCLamportMutex or Philosophers. The cost left is the shape of the closure
tree rather than any one hot spot. Per Commit successor (about 1,500 instructions after #73 and #75):

- a quarter in the walk's own segments and continuations (loops over ops, `Result` plumbing, a
  prologue and epilogue per dynamic call);
- a fifth in memo lookups (the lookup closure, then the probe);
- a sixth in fingerprints;
- the rest in guards and the store.

On MCLamportMutex and btree, roughly a third of the instructions are closure entry and exit and
`Leaf` dispatch around store calls that are themselves short. A JIT that compiles whole walks
removes that dispatch, and it can inline the store's fast paths (a tuple or an integer run applied
to an integer, two scalars compared by id, a packed memo probe) where today each is a call. The
options weighed:

| Option | Gain | Code and risk |
|---|---|---|
| More fused closures | 2–8% per shape, falling | small; done through #75 |
| Bytecode with superinstructions | negative (DESIGN.md §3.1 measured a match-loop VM 3–5× slower than fused closures; stable Rust can't guarantee threaded dispatch) | medium |
| Our own native backend, whole walks | 25–45% of instructions on the laggards (§7) | large: two ISAs, executable memory on three OSes, a new `unsafe` surface |

Only the third reaches the gate on all six, so it's the proposal. The closures stay: they are the
fallback for everything the backend doesn't emit, the reference the backend is tested against, and
the only path where executable memory isn't available.

## 2. Scope

In order of the stages in §8:
- **Predicates:** guards and invariants (the `Predicate` trees of `predicate.rs`: `=`, `#`, `~`,
  `/\`, `\/`, `=>`, `\in`), and quantifiers over intervals and constant sets (`quantify_intervals`,
  `\A x \in S : P` with S constant).
- **Whole walks:** segments, `exists_step` over sets and intervals, disjunctions, `either_step`, the
  shortcut, `x' \in S`, and the continuation that reaches `on_complete`. A walk compiles to one
  function per action, whose successors call back into the search through one fixed entry,
  `visit_successor`.
- **Memo lookups:** the table check, the key reads and the packed probe for widths 1 and 2, inline.
  The table's state stays in `MemoTable`, so a miss, a store, probation and switching a table off
  stay the existing Rust, called from the code.
- **Fingerprints:** the successor's combine over its variables, unrolled by the state's width, with
  the per-value fingerprints still from `Fingerprints::get_child`. The expected gain here is small
  (§7); this comes last and only if measured worthwhile.

Out of scope: liveness, symmetry, VIEW, printing, `TLCGet`/`TLCSet`, the lazy sets, recursive
operators, and the bridged builtins. They keep running as closures, called from the code.

## 3. What it compiles from: the closure compiler's decisions, as a small IR

The backend does not re-derive semantics from the engine IR. The closure compiler already decides,
node by node, the shape (`Shape`, `Leaf`, `Predicate`), the footprint, what is memoised, and what
the walk knows is assigned on each path. That compiler emits a second product, a **native IR
(NIR)**, beside the closures, from the same decisions in the same places:

- NIR is a list of functions, each a sequence of basic blocks over virtual registers holding
  `Id`s (u32) and booleans.
- Its instructions are few: read a variable, slot or primed variable; constants; compare ids; the
  kind and payload of an id from the store's `Meta`; a tuple or an integer run applied to an
  integer; a packed memo probe; branches; assign, test and unassign a variable; and two kinds of
  call. A **helper call** goes to an `extern "C"` Rust function such as `Store::apply`,
  `Store::equals`, `Store::is_member` or `MemoTable::set`. An **eval call** goes to any existing
  `Eval`, `Test` or `Step` closure, through one trampoline.
- **Fallback is per node.** A node the NIR lowering doesn't handle becomes an eval call to the
  closure the compiler already built for it, so every walk compiles, with coverage growing a
  shape at a time. A walk whose NIR is mostly eval calls isn't emitted at all (the threshold is
  measured, not guessed), and stays a closure.
- **Bails.** Every helper and eval call returns a status beside its value. On a bail the code
  writes the reason to `Machine` and returns, through the unassigns of each segment it's in, which
  the NIR spells out as the closures do. So a bail stops where it stops today, for the same
  reason, with the same states assigned.
- The NIR is plain data (a `Vec` of enums). It's printable, so a test can check the NIR of a
  model, and the emitters are pure functions from NIR to bytes.

## 4. Emitters: x86-64 and aarch64

- **Register model.** A fixed frame: virtual registers spill to a stack slot each, and a simple
  linear-scan pass keeps the hottest in callee-saved registers. `Machine`'s `cur`, `next` and
  `locals` and the store's `meta` and `heap` bases are kept in fixed registers.
- **Bases go stale after a call.** The store's `meta` and `heap` are growable `Vec`s (`allocate`
  pushes to `meta`, interning extends `heap`), and `next` and `locals` are `Vec`s too. So the
  bases are reloaded from `Machine` after every helper or eval call: any of them may intern a
  value, including an interval's integers, as `quantify_level` does. Straight-line code between
  calls, where the fast paths live, keeps them in registers. A call that can't allocate is marked
  as such in NIR and keeps them. The reload is two or three loads. Moving the store onto DESIGN.md
  §2.6's arena, with stable addresses, would remove it, but it isn't a prerequisite.
- **Calls** follow the platform ABI: System V on Linux and macOS x86-64, Win64 on Windows,
  AAPCS64 on aarch64 (with Apple's variant on macOS arm64).
- **Encoding.** One module per ISA with a small encoder for the instructions NIR needs (about 40
  forms on x86-64, about 35 on aarch64), and labels with fix-ups for branches. Each form is tested
  against bytes taken from the architecture manuals and checked once against a system
  disassembler (`objdump`, `llvm-objdump`) in a test that only runs where one is installed. None is
  a dependency.
- **No self-modifying code, no inline caches.** A function is emitted once, before the search,
  and never patched.

## 5. Executable memory, per OS, and W^X

Code is written into memory that is writable and not executable, then made executable and not
writable before it ever runs. Nothing is writable and executable at once, except where macOS arm64
requires its own scheme:

| OS | Map | Seal | Instruction cache |
|---|---|---|---|
| Linux x86-64 | `mmap(PROT_READ \| PROT_WRITE, MAP_PRIVATE \| MAP_ANONYMOUS)` | `mprotect(PROT_READ \| PROT_EXEC)` | coherent; nothing to do |
| Linux aarch64 | as above | as above | `dc cvau` / `dsb ish` / `ic ivau` / `dsb ish` / `isb` over the range, in `core::arch::asm!` |
| macOS arm64 | `mmap(..., MAP_PRIVATE \| MAP_ANON \| MAP_JIT)` | `pthread_jit_write_protect_np(0)` while writing, `(1)` after; per thread | `sys_icache_invalidate` |
| macOS x86-64 | `mmap` with `MAP_JIT` | `mprotect` | coherent |
| Windows x64 | `VirtualAlloc(MEM_COMMIT \| MEM_RESERVE, PAGE_READWRITE)` | `VirtualProtect(PAGE_EXECUTE_READ)` | `FlushInstructionCache` |

The functions are declared `unsafe extern "C"` in our code, from libc, libSystem and kernel32,
which std already links. No crate is needed.

- **Where executable memory is refused,** the backend is off and the closures run, with a line
  under `PROVE_IT_ENGINE=debug`. That covers an `mmap`/`mprotect` failure (SELinux `execmem`, PaX,
  a hardened container), `MAP_JIT` refused on macOS (a signed host without
  `com.apple.security.cs.allow-jit`), or any failure in the checks of §6.
  - Node and Bun both JIT and carry that entitlement. Whether a `bun build --compile` binary keeps
    it once signed must be checked on macOS before stage N4, and the result recorded here.
- Memory is mapped per search and freed when the search ends; nothing outlives the `Program` that
  emitted it.

## 6. Containing `unsafe`, and proving parity

`unsafe` lives in one module, `tla-engine/src/native/`, in three small files. Everything else is
safe code:
- `memory.rs`: map, seal, flush and free (§5), about 150 lines across the OSes.
- `call.rs`: the one place a code address becomes a function pointer and is called. It checks the
  address lies inside a sealed mapping this search owns, and the signature is fixed:
  `extern "C" fn(*mut Machine, *mut Continue) -> u32`.
- `helpers.rs`: the `extern "C"` helpers. Each takes `*mut Machine`, turns it back into `&mut`
  under one documented invariant (the code is only ever called from `call.rs`, on the thread that
  owns the `Machine`), and calls the existing safe Rust.

The NIR lowering, the register allocator and both encoders are safe code that only produces
`Vec<u8>`, so a bug there can make wrong code but not unsound Rust. That's what the parity checks
are for:
- **Off by default, behind a setting.** `PROVE_IT_NATIVE_CODE=on|off|verify`, default `off` until
  stage N6. `verify` runs each compiled predicate and the closure it replaces on every state, and
  panics on any difference in value or bail, as `PROVE_IT_FP_VERIFY` does for fingerprints.
- **The differential and state logs, on and off.** Parity's Differential and Engine coverage gain
  a pair, `rust-native/rust`: full stdout and the state log with the backend on, against the
  closures, on all 1,466 runs and 733 models. As for every pair, a new difference fails it.
- **A std-only differential fuzzer** in `cargo test`, seeded and deterministic: it generates
  predicates and walks from the NIR's own vocabulary over random small stores and states, runs
  them as closures and as native code, and compares value, bail reason, assigned variables and
  successor order. A long-running version runs nightly on Depot. The existing `cargo fuzz` crate
  stays a separate workspace with its own dependency, as now.
- **Encoder tests** against known bytes (§4), and a test per OS of the mapping lifecycle: map,
  write, seal, run, free, and confirm a write after sealing faults in a child process.
- **The Platforms workflow** runs the native tests and the unit suite with the backend on, on each
  OS the stage supports. With it off elsewhere, the closures still run there.

## 7. Expected gain per laggard

From the callgrind profiles behind #53–#75: the instructions in closure entry and exit, `Leaf`
and `Op` dispatch, `Result` plumbing and segment loops, plus the store fast paths that become
inline. Ranges, since the register allocator's quality decides where in each range a model lands:

| Model | Dispatch and inlinable fast paths | Expected instructions saved | Wall-time ratio vs TS now → expected |
|---|---|---|---|
| Commit | ~55% | 25–35% | 0.94× → 1.25–1.4× |
| btree | ~40% (fingerprints a fifth, untouched until N5) | 20–30% | 1.01× → 1.25–1.4× |
| SimpleRegular | ~45% | 25–35% | 1.13× → 1.4–1.6× |
| MCLamportMutex | ~50% | 25–40% | 1.08× → 1.35–1.6× |
| Philosophers | ~60% | 30–45% | 1.23× → 1.6–1.9× |
| MCBakery | ~45% | 25–35% | 1.48× → 1.8–2.1× |

Wall time also carries a fixed 40–60 ms of start-up shared by both engines, which caps the ratio
on the short models (Philosophers, Commit). Emitting costs well under a millisecond per kilobyte
of IR, so it's paid on every run rather than kept for long ones. It is measured in N1, and
skipped below a size or time threshold if it ever shows on short runs.

## 8. Milestones

Each milestone is a few small PRs, each with Compare and Parity as now. No milestone turns the
backend on by default except N6.

- **N0, harness.**
  - The setting.
  - `rust-native/rust` in the differential and engine coverage, which equals `rust/rust` until
    there's code.
  - The NIR types and the lowering, emitting nothing yet but printable.
  - The fuzzer's generator.
- **N1, x86-64 Linux only, predicates.**
  - `memory.rs` and `call.rs` for Linux, the x86-64 encoder, guards and invariants as native
    code, and eval calls for the rest.
  - Gate: parity, no slowdown on any suite model, and a measured gain on MCBakery and
    MCLamportMutex.
- **N2, x86-64 Linux, whole walks.**
  - Segments, `exists_step`, disjunctions and the continuation, plus inline memo probes.
  - Gate: the six laggards at 1.3× over the TypeScript engine on Depot.
- **N3, aarch64 Linux.**
  - The aarch64 encoder and the icache flush.
  - The Linux arm64 Depot runner in Parity.
- **N4, macOS (arm64 and x86-64).**
  - `MAP_JIT`, `pthread_jit_write_protect_np` and `sys_icache_invalidate`.
  - The entitlement check of §5 for the compiled binary.
  - Platforms on macOS with the backend on.
- **N5, Windows x64, and fingerprints.**
  - `VirtualAlloc`, `VirtualProtect` and the Win64 ABI.
  - The fingerprint combine, if N2's profiles still show it worth a stage.
- **N6, default on** where executable memory is granted, after a full conformance run and a
  release with it on behind the setting.
