# The front end (`tla-front`), as built

The plan, the API and the milestones are in [DESIGN.md section 14](../DESIGN.md). This file holds
what each milestone built and measured, in the order they landed.

## F1 as built

- `crates/tla-front` with `lexer`, `errors`, `json` and `hash`, and the `front-dump` binary.
  `tokenize` returns the tokens with their texts interned as `Rc<str>`, as `lexer.ts` keeps each
  name one string object, so later stages compare names by pointer where TypeScript does.
- `scripts/front-differential.ts tokens`: 2,356 of 2,356 modules match (the 304 fixtures and the
  2,052 corpus modules), and so do 2,400 modules made by inserting and deleting text at random in
  800 corpus modules, 448 of which the lexer rejects, so its errors and their positions are held
  too. `cargo test` covers tabs, UTF-16 columns, synonyms, steps and every error kind without the
  corpora.
- Speed, best of five in process, on this 4-core machine: `TE.tla` (2.9 MB) 50 ms against
  95 ms for `lexer.ts` in Bun; `tcp_proof.tla` (259 KB) 3.2 ms against 12.6 ms; `LevelSpec.tla`
  (132 KB) 0.45 ms against 5.6 ms.

## F2 as built

- `ast` mirrors `ast.ts` type for type. A node TypeScript reaches from two places is one `Rc`:
  the set of `\A x, y \in S` in both bounds, a theorem's or assumption's statement and the
  definition its name makes, a module's definitions and its units. Later stages that key on
  identity, as the IR lowering does, see the same sharing. Ranges are values, not `Rc`s.
- `parser` ports the `tlc` and `sany` modes of `parser.ts` (`parse_module`,
  `parse_module_tokens`, `parse_sany_module`) and `extractModule`. The `tlapm` mode, which reads
  proof obligations as tlapm does, is left out: the checker never uses it. A module named by a
  keyword makes `parser.ts` run SANY's own parser (`getSanyParseError`), which F5 ports; until then
  the Rust parser returns an `unsupported:` error there, and no corpus module reaches it.
- `dump` writes the AST and errors as canonical JSON: keys sorted, `undefined` fields left out, so
  the harness compares the two ASTs as text without either side building objects in the other's
  order. `scripts/front-differential.ts` gains the modes `ast` and `sany-ast`, `--mutate <n>`
  (four variants of each of the first n modules, inserting TLA+ syntax and deleting text at places
  a fixed seed picks, so errors and their positions are compared too), and `time`.
- **Parity.** `ast` and `sany-ast`: 2,356 of 2,356 modules match, and so do 6,000 variants of
  1,500 randomly chosen corpus modules (1,488 of the first 2,000 rejected), with every error's
  message, reason and position, and the SANY errors of `HIDE`. Verification's Front End job runs
  all three modes with `--mutate 400`.
- **Speed** (`front-differential.ts time`, best of five, tokens and AST, this 4-core machine):
  all 2,356 modules 996 ms in TypeScript against 397 ms in Rust; `TE.tla` 337 against 216 ms,
  `tcp_proof.tla` 39 against 12.6 ms, `FindOp.tla` 10.9 against 2.7 ms. Under callgrind, about
  a third of Rust's time is the allocator (an `Rc` per node, a `Vec` per argument list) and a
  sixth is dropping the AST, which the binary can skip at exit. An `ExpressionKind` is 160 bytes,
  set by the qualified `Apply`'s ranges; boxing them is the next step if parsing shows up in a
  whole front end's profile.

## F6 as built

- `config` ports `parseConfig`: TLC's `ModelConfig.parse` over the tokens TLC reads with SANY's
  lexer, for TLC master and 1.7.4 (TYPE and TYPE_CONSTRAINT, none of the later keywords), and
  JavaCC's lexical errors (`formatLexicalError`, `escapeLexeme`), whose columns and escapes count
  UTF-16 code units. `ModelConfig` keeps `config.ts`'s fields; `ConfigError` is `TlaConfigError`.
- `front-differential.ts config` runs over every `.cfg` of the corpora and fixtures, writing each
  file's configuration (or error) for both versions on one line: 1,425 of 1,425 match, and so do
  5,700 variants from `--mutate`, and 3,324 more variants made to hit the lexer (unterminated
  strings and comments, characters outside the BMP), of which 2,620 are errors (10 kinds of
  message, counting the keyword named as one).

## F3 as built (the texts)

- The standard modules are the strings of `src/sany/modules.ts` (SANY's, for TLC master and
  1.7.4) and `src/bundled-modules.ts` (the Reals, RealTime and Toolbox TLC bundles, which differ
  from SANY's copies by a final newline). `scripts/front-modules.ts` writes each to
  `crates/tla-front/modules/<set>/<Name>.tla`, with `src/standard_modules.rs` including them, and
  `--check`, which Verification's Front End job runs, fails when a copy differs from the
  TypeScript string. The copies are generated, so the TypeScript stays the one place to change a
  text until it is retired, when the `.tla` files become the source.
- `get_standard_module(name, version)` reads them; `cargo test` parses all 33 in SANY's mode.
- Left for F4, with resolution: the module loader (`createTlcOrder`'s search of the spec's
  directory, the root file's extracted modules, the user's copies of standard modules TLC reads
  first) and the tables that go with the texts (`STANDARD_LEVELS`, `USER_STANDARD_MODULES`).

## F8 slice 1a as built (linking and resolution, without instances)

- `resolve` ports `resolve.ts` whole: binding, `isBindable`'s errors and warnings, labels,
  selections of a theorem's or step's parts, substitutions, `collectSemanticErrors` and
  `resolveModule`. What the TypeScript resolver writes on the AST, the Rust one writes in each
  node's `resolved` cells (`key`, `is_local`, `is_recursive`) and a definition's
  `is_self_referential`, so a copy of a node carries them as a spread TypeScript node does. The
  `WeakSet`s and `WeakMap`s keyed by node (`selections`, `selectionErrors`, `renamedArities`) are
  tables keyed by the node's address that keep the node alive.
- `environment` ports the linking of `createEnvironment` for a spec without a model that SANY
  accepted: the module loader, one parse per text, rejected literals, EXTENDS, standard modules
  (their builtins come from `src/standard_builtins.rs`, which `scripts/front-modules.ts` writes
  from `getStandardModule` and `CORE_OPERATORS` and checks in CI), a user's module that replaces a
  standard one, nested modules, cycles, the root's names for its definitions, and the variable
  index. `ordered_map` keeps a JavaScript `Map`'s order, which the environment's maps follow.
  An INSTANCE (at the top, in a LET, or in a proof) and a name that selects a subexpression
  return `NotYet`; slice 1b ports `instances.ts` and `subexpressions.ts`.
- `front-differential.ts resolve` links every module of the corpora and fixtures as a spec's root
  and compares the environments as canonical JSON: each definition by key with every name
  resolved, the builtins with their flags, the variables and their indices, the root's constants,
  SANY's errors and warnings. 1,771 of 2,356 modules match and 585 are not compared yet (an
  INSTANCE, a selecting name, or a module SANY's parser rejects, which F5 ports); with
  `--mutate 400`, 3,268 of 3,956. None differ. Verification's Front End job runs it.
