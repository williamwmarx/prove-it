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

## F8 (the lowering): the slices, and where each starts

`ir.ts` (IR 8 at 148cdae) reads, for every node it writes, the resolved environment: so the
lowering lands after the part of resolution it reads, in four slices, each one PR gated on the
corpus (the 641 IRs `bun scripts/run.ts engine-ir` writes, and the 30 goldens in `cargo test`):

1. **Environment, the subset the IR reads.** What `lowerToIr` calls: `environment.variableIndex`,
   `constants` (names), `substitutions`, `definitions` (by key, instance copies included, as
   `environment.ts` builds them in `createEnvironment` with `linkModule`, `createLocalFunction`,
   `getVariableIndex`), `builtins` (name, arity, `isStateLevel`, `isLevelConstant`, `isLazy`:
   `standard-modules.ts`, `CORE_OPERATORS`), `substitutedDefinitions`, and each node's
   `resolution` (`resolve.ts` `resolveModule`, which sets `LOCAL_RESOLUTION` at line 735, and
   `subexpressions.ts`), plus `isImpureDefinition` and `hasRepeatedEffect` (`dependencies.ts`)
   for the definition flags. Gate: `front-differential resolve`, each model's definition keys,
   substitutions, builtins and every node's resolution as canonical JSON, run by Verification's
   Front End job as a permanent gate. `resolve.ts` also
   reports SANY's semantic errors; the subset ports them as it meets them, F5 finishes them.
2. **Nodes and definitions.** `writeNode`, `writeDefinition` and the reach order (the model's
   roots, then breadth-first through definitions and scopes), into `tla_ir`'s structures, encoded
   by `tla_ir::encode`. A node met again is a reference, which the AST's `Rc` sharing gives
   (`Rc::ptr_eq` where `ir.ts` keys a `Map` on the object). Gate: decode both IRs with `tla-ir` and
   compare their definitions and nodes.
3. **Texts, variables, builtins, constants, scopes.** The text table is `createTlcOrder`'s ranked
   strings (`tlc/order.ts`), then the rest in first use; constants from the configuration in
   `transfer.ts`'s encoding (`createStateEncoder`), which needs no evaluator. Gate: those
   sections equal.
4. **The model.** Init, Next, the configuration's names, invariants and property invariants with
   their names (IR 6), constraints, VIEW, settings, and TLC's actions with their labels (IR 5).
   Gate: whole IRs byte-equal. Four inputs are evaluated in TypeScript today: SYMMETRY's
   permutations, the action split over constant `\E` bounds, startup values, and the liveness
   atoms and formula; a model that needs one gets `NotYet` until the engine's startup phase
   (DESIGN section 14, which the CLI session owns) and `tla-live` compute them in Rust, with no
   TypeScript involved, and the harness counts those.
