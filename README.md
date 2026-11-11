# Prove It

Prove It checks TLA+ specs and TLAPS proofs without the JVM. It is a drop-in for TLC, SANY and tlapm: it takes their options and prints what they print, byte for byte. On one worker it runs 4 to 31 times faster than TLC.

```shell
bun add @atemp/prove-it
```

```shell
prove-it Spec.tla            # TLC's options
prove-it tlapm Module.tla    # tlapm's options
```

## Speed

Wall-clock time for a whole run, startup included, as the median of five runs on a 4-core machine. Every timed cell reports TLC's verdict, distinct states, depth and generated states.

| Model | Distinct states | TLC, 1 worker | TLC, 4 workers | tla-ts | tla-rs | Prove It, 1 worker | Prove It, 4 workers | Prove It over TLC, 1 worker each |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| btree/MCbtree | 374,727 | 22.31 s | 7.39 s | 9.35 s | fails | 0.72 s | 0.28 s | 31x |
| lamport_mutex/MCLamportMutex | 724,274 | 9.66 s | 4.96 s | 12.92 s | 130.44 s | 2.25 s | 1.02 s | 4x |
| summerset paxos/Paxos_MC | 17,153 | 6.13 s | 2.54 s | 7.66 s | fails | 0.57 s | 0.59 s | 11x |
| Bakery-Boulangerie/MCBakery | 655,200 | 6.05 s | 4.44 s | 8.30 s | fails | 0.79 s | 0.52 s | 8x |
| Commit | 282,251 | 4.14 s | 2.02 s | 3.73 s | 15.09 s | 0.30 s | 0.13 s | 14x |
| ccf consistency/MCSingleNode | 63,449 | 3.78 s | 1.83 s | 2.70 s | 14.18 s | 0.46 s | 0.24 s | 8x |
| TeachingConcurrency/SimpleRegular | 277,726 | 2.99 s | 1.81 s | 3.12 s | 18.23 s | 0.50 s | 0.25 s | 6x |
| Disruptor/MCDisruptor_MPMC | 112,929 | 2.72 s | 1.34 s | 2.61 s | fails | 0.19 s | 0.17 s | 14x |
| ReadersWriters/MC (liveness) | 21,527 | 1.65 s | 1.39 s | 1.86 s | fails | 0.09 s | 0.10 s | 19x |
| ewd426/TokenRing (liveness) | 46,656 | 1.39 s | 1.11 s | 1.57 s | 0.99 s | 0.20 s | 0.12 s | 7x |

Over the eight models that take TLC more than two seconds, Prove It on one worker is 10 times faster than TLC on one worker at the geometric mean, and 2 to 10 times faster than TLC on all four cores. On the smallest models, where TLC takes about half a second, the ratio reaches 44 times, but most of that is the JVM starting.

Prove It gains less from more workers than it should on models this small: four workers are 1.5 times faster than one at the geometric mean, and no faster on Paxos_MC and ReadersWriters.

TLC is built from `tlaplus/tlaplus` d8fb231 and runs on JDK 21, [tla-ts](https://github.com/aidenybai/tla-ts) is 0.0.10 on one worker under Node 24, and [tla-rs](https://github.com/fabracht/tla-rs) is 0.24.11, which has no parallel mode. tla-rs fails five of these models: two do not parse, two stop on an evaluation error, and one was killed at 15.6 GB of memory. The machine is a Depot `depot-ubuntu-24.04-4` runner (AMD EPYC 9R45, 16 GB). The benchmark runs weekly on eighteen models; [`.depot/README.md`](https://github.com/williamwmarx/prove-it/blob/main/.depot/README.md#benchmark) describes it and how to run it.

## What to expect

**The same answer as TLC.** Prove It is compared against recorded TLC output on the `tlaplus/Examples` corpus and TLC's own tests. Where it cannot yet match TLC on a spec, it says so and stops with `prove-it: not native yet: <reason>` rather than print something different.

**Nothing to install but the package.** The engine is Rust. npm installs a native build for Linux (x64 and arm64, glibc and musl), macOS (arm64 and x64) and Windows (x64), and the package carries a WebAssembly build for the browser and every other platform.

## As a library

```ts
import { check } from "@atemp/prove-it";

const result = await check({
  source: `---- MODULE Counter ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = x + 1
Small == x < 3
====`,
  config: "INIT Init NEXT Next INVARIANT Small",
});

result.status; // "invariant-violation"
```

`prove` checks a module's proofs the same way. Both run in Node, Bun and the browser.

## Development

The repository is a Bun workspace. The Rust workspace in `packages/prove-it/native` is the product, and `packages/prove-it/src` is the npm package around it. Install [Bun](https://bun.com) 1.4.4, Node 22 and the Rust toolchain that `packages/prove-it/native/rust-toolchain.toml` pins, then:

```shell
bun install
bun run test          # builds the package and the native engine first
bun run typecheck
bun run lint
bun run format:check
```

[`AGENTS.md`](https://github.com/williamwmarx/prove-it/blob/main/AGENTS.md) says what matters when changing the code, and [`DESIGN.md`](https://github.com/williamwmarx/prove-it/blob/main/packages/prove-it/native/DESIGN.md) explains how it is built.

## Credits

Prove It began as a fork of [tla-ts](https://github.com/aidenybai/tla-ts) by Aiden Bai. Its semantics follow TLC, SANY and tlapm, and its provers are ports of Zenon, Isabelle/TLA+ and Z3; see [`THIRD_PARTY_NOTICES.md`](https://github.com/williamwmarx/prove-it/blob/main/THIRD_PARTY_NOTICES.md).

## License

MIT
