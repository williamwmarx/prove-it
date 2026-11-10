# Prove It

Prove It interprets and model checks TLA+ specs in TypeScript, without the JVM. It reproduces TLC's output and checks TLAPS proofs with its own provers. It runs in Node, Bun and the browser.

Prove It is derived from [tla-ts](https://github.com/aidenybai/tla-ts) by Aiden Bai, under the MIT license.

```shell
bun add @atemp/prove-it
```

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

The command line takes TLC's options, and `prove-it tlapm` takes tlapm's:

```shell
prove-it Spec.tla
prove-it tlapm Module.tla
```

`check` searches with a native engine written in Rust. npm installs it as an optional package for Linux (x64 and arm64, glibc and musl), macOS (arm64 and x64) and Windows (x64), and the main package carries it as WebAssembly for the browser, for any other platform and for an install without optional dependencies. Where no engine loads, `check` throws `EngineUnavailableError` and the command line exits with 255; `PROVE_IT_ENGINE=0` checks with the interpreter instead, which needs no engine and is much slower.

## Development

The repository is a Bun workspace, and the library lives in `packages/prove-it`. Install [Bun](https://bun.com) 1.4.4, Node 22 and the Rust toolchain that `packages/prove-it/native/rust-toolchain.toml` pins, then:

```shell
bun install
bun run build         # bundle dist/ and emit its type declarations
bun run typecheck
bun run lint
bun run format:check
bun run test          # builds dist/ and the native engine first, which the tests run
```

`bun run build:binary` in `packages/prove-it` compiles the CLI into a standalone executable, `dist/prove-it`, with its code compiled to Bun bytecode, which starts faster than `dist/cli.js`.

The conformance and benchmark scripts bundle with Bun and run under Node, whose V8 is much faster than JavaScriptCore on the SMT prover. Run them from `packages/prove-it`:

```shell
bun run conformance:fetch
bun run conformance
TLA2TOOLS_JAR=/path/to/tla2tools.jar bun run bench
TLA2TOOLS_JAR=/path/to/tla2tools.jar bun run bench:corpus
```

## License

MIT
