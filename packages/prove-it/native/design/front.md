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

## F8 slice 1b as built (instances and selecting names)

- `instances` ports `instances.ts`: `mapChildren` and `mapDefinition` in the order TypeScript's
  object literals evaluate their fields (copies are made in that order, and their keys count up
  in it), `substitute` with its three modes for ENABLED, the renamer, and `withLetInstances`.
  `sourceNames` is a table by address, as the `WeakMap` is, so a spread copy doesn't carry it.
- `subexpressions` ports `subexpressions.ts`: the selection of a definition's, label's, LET's or
  operand's part, with SANY's errors for a name that selects nothing.
- `environment` links an INSTANCE at the top of a module (its copies under `Name@Module#n`, the
  names it adds, qualified or not, and the definitions an instance with substitutions makes, which
  the IR flags), a LET INSTANCE (its definitions put in the LET), and an INSTANCE in a LET or a
  proof that resolution meets, interleaved with nested modules in the order of the text.
- `front-differential.ts resolve`: 2,331 of 2,356 modules match, up from 1,771, and none differ;
  with `--mutate 400`, 3,931 of 3,956. The 25 left are modules SANY's parser rejects (F5).

## F8 slice 1c as built (the definitions' facts)

- `dependencies` ports `dependencies.ts`: each definition's local facts and its edges, closed over
  the call graph with Tarjan's algorithm, which the IR's repeated-effect flag and the model's
  printed roots read (`has_repeated_definition_effect`, `has_repeated_effect`).
- `front-differential.ts resolve` compares each environment's rows of facts too: all match.

## F8 slice 1d as built (the model's configuration)

- `environment` takes the model's configuration: the constants it assigns (by key, scoped to a
  module or not), the operators it gives a value or a table of values (builtins), its
  substitutions, the overrides that a module-scoped entry makes of every instance copy, and TLC's
  configuration errors, word for word. Two cases return `NotYet`: several unassigned constants,
  which TLC reports in SANY's order of declarations (F7), and a substitute TLC evaluates at
  startup (the engine's startup phase, which the CLI session plans in `design/cli.md`).
- `front-differential.ts model` links each corpus model, a `.cfg` file and the spec beside it:
  1,092 of 1,111 match and none differ; with `--mutate 400` (variants of the configurations),
  2,682 of 2,711. Verification's Front End job runs it.

## F8 slice 2 as built (nodes and definitions)

- `lower` ports the core of `lowerToIr` into `tla_ir`'s structures: each node in prefix order as
  the blob holds it, a node met again as a reference, LET definitions inline and the others in
  the order the model reaches them, names with their resolutions and caches, builtins, texts in
  the order of their first use after the ranked ones, and how each junction is written (IR 9: a
  bulleted list, or where each prefix of an infix chain ends). A constant's value (slice 3) and a
  startup value (the startup phase) aren't written yet.
- `front-differential.ts ir` lowers each module's environment, on both sides, as a model whose
  Init and Next are a placeholder and whose configuration names every definition by key as an
  invariant, with no text ranked, and compares the IRs byte for byte: 2,332 of 2,357 modules
  match and none differ; with `--mutate 400`, 3,932 of 3,957. Verification's Front End job runs
  it. Slices 3 and 4 add TLC's string order, the values and the model's own roots.

## F8 slice 3a as built (TLC's orders)

- `order` ports `createTlcOrder` (F7's order): the module set TLC reads (TLC's own module texts,
  which `scripts/front-modules.ts` now writes to `modules/tlc` with SANY's and TLC's interned
  texts in `src/tlc_data.rs`), SANY's symbol table per module as `java.util.Hashtable`
  enumerates it, TLC's string order (the configuration's values, TLC's startup strings, each
  module's tokens in the order SpecObj parses the modules, the string literals, TLC's runtime
  strings), the root module's declarations in SANY's order, and each module's definitions in the
  order TLC computes them.
- `front-differential.ts order`: all 1,111 corpus models match, and all 2,711 with
  `--mutate 400`. Verification's Front End job runs it. The lowering ranks texts by this order
  once the model section (slice 4) is in.

## F8 slice 3b as built (the configuration's values)

- The environment keeps the configuration's values, and the lowering writes each constant with its
  value in `transfer.ts`'s encoding: a set sorted and its duplicates dropped as `createSet` does,
  strings and model values compared by their rank in TLC's string order, and the encoder's strings
  as texts after the nodes'. Values TLC can't compare (mixed kinds, differently typed model values)
  return `NotYet`; the startup phase will word their errors.
- `front-differential.ts model-ir` ranks the texts in TLC's string order, as `check.ts` does, links
  each corpus model with its configuration, and lowers its environment as `ir` does: 1,097 of
  1,111 models give byte-identical IR and none differ; with `--mutate 400`, 2,694 of 2,711.
- With TLC's orders in, a configuration that leaves several constants unassigned is reported as
  TLC reports it, by the first in SANY's order of declarations: `model` now matches 2,694 of
  2,711 with `--mutate 400`, up from 2,682.

## F8 slice 4 in progress (the model section, on `native-parity`)

- The environment lists the definitions TLC computes at startup, in `environment.ts`'s order, and
  the assumptions of the root module and those it extends; `describe_range` names an assumption as
  TLC prints it. `front-differential model` compares both.
- `spec` ports `getLevel` (`liveness.ts`), the scopes an instance or an operator's arguments give a
  formula (thunks, closures, a LET's own scope, and literal or configured values),
  `getSpecification` and `expandTemporal`, and `getProperties`. The `spec` mode compares the split
  of SPECIFICATION (1,093 of 1,111 models) and the `properties` mode the sorted properties (1,032
  of 1,111), none differing. What TLC evaluates there (a constant conjunct or definition, a `\A`
  a property unrolls over a constant set) is `NotYet`.
- `Lowering::write_model` writes the model section in `lowerToIr`'s order, and the scopes
  interleaved with the definitions as `ir.ts` writes them. `model::lower_model` lowers a model
  from its files for the native binary. The `model-full` mode compares the whole IR with
  `lowerToIr`'s, without TLC's actions, which the engine's startup phase splits: 676 of 1,111
  models are byte-identical, none differ. Still `NotYet`: temporal properties and fairness (the
  liveness formula and atoms), SYMMETRY (the engine's startup phase), scoped properties, and the
  evaluations above.

## (d1) as built: what SANY prints (`report.rs`)

`report::get_sany_text` writes what `getSanyReport` prints while TLC runs SANY on a spec that SANY accepts without a message. That covers the "Parsing file" lines in the order `SpecObj.loadSpec` reads the modules, the "Semantic processing" lines in `calculateDependencies` order, and the "Linting" lines. The caller describes each file through `describe_file(name, origin)`, so the CLI keeps `createFileDescriber`'s temporary paths.

It returns `NotYet` in these cases, which (d2) and (d4) take on:

- SANY's parse errors;
- a file named apart from its module;
- a missing module;
- a circular dependency;
- linking's semantic errors or warnings;
- PlusCal;
- any record field named like a symbol of a loaded module.

The last case is a conservative stand-in for SANY's linter. On the corpora it holds back 150 specs, and only 25 of them really warn.

The `sany-text` gate (`front-differential.ts sany-text`) describes files as `name|origin` on both sides. It reports 1,716 of 2,357 matching and 636 not compared yet.

The mutated variants all come back `NotYet`, because their files are named apart from their modules.

## (d2) part 1 as built: SANY's level checks (`levels.rs`)

`levels.rs` ports `src/levels.ts` and `src/substitution-levels.ts`, which compute on the AST the levels, weights and Leibniz flags SANY does, and report its level errors. The linker runs them when `EnvironmentOptions.is_level_checked` is set, as `createEnvironment` does without `isSanyAccepted`. That covers each module's definitions, assumptions and theorems, and the substitutions of every INSTANCE, in the order SANY reports them.

`get_sany_text` links with the checks, so a spec with a level error comes back `NotYet` instead of printing a clean parse. The `levels` gate compares the linker's result with TypeScript's `createEnvironment` with level checks on: 2,332 of 2,357 match, and 3,932 of 3,957 with `--mutate 400`, with 0 differing. The 25 left are the ones `resolve` doesn't compare yet.

The corpora exercise these errors, with SANY's wording:

- actions in a temporal formula;
- `[]` or `<>` followed by a raw action;
- action-level bounds;
- non-constant steps of a temporal proof;
- arguments over an operator's levels;
- the levels and Leibniz checks of instance substitutions.

With the checks, `sany-text` reports 1,716 of 2,357 matching and 0 differing.

## (d2) part 2 as built: SANY's fatal errors

`get_sany_text` writes the fatal errors that stop SANY's parsing phase, other than parse errors:

- a module no file holds, reported in the module that names it;
- a circular dependency, found before semantic analysis;
- a file named apart from the module it holds.

It prints them as `getSanyReport` does, after the "Parsing file" lines so far. `ReportOptions.file_name` is the name TLC gives SANY for its "Fatal errors while parsing TLA+ spec in file" line.

TLC 1.7.4's aborts and SANY's parse errors (`src/sany/parse-error.ts`) are still `NotYet`.

`sany-text` reports 1,825 of 2,357 matching, and 2,117 of 3,957 with `--mutate 400`, with 0 differing.

## (d2) part 3 as built: SANY's semantic errors and warnings

SANY goes on analyzing after a module with errors. After each module it prints every message so far: the warnings, then "Semantic errors:" and the errors. It level-checks a module only while no module so far has an error.

`environment::get_sany_messages` links in a collecting mode, which does this:

- It keeps each top-level module's errors and warnings instead of stopping at the first module with errors.
- It defers the level checks, then runs them in SANY's order of analysis, which the caller gives.
- It reports "Substitution error, probably due to error in module being instantiated." at each INSTANCE of a module with errors, as `Generator.createSubstIn` does.

`get_sany_text` prints the messages cumulatively, as `getSanyReport` does, and skips linting when there are errors.

Still `NotYet`:

- TLC 1.7.4's message layout;
- an error that stops linking itself;
- a definition whose arity differs from its RECURSIVE declaration. SANY applies the declared arity, and neither resolver models this.

Porting this showed that both resolvers saw a module's own declarations before they're declared. That is fixed in `resolve.ts` and `resolve.rs`.

`sany-text` reports 1,886 of 2,357 matching, and 2,175 of 3,957 with `--mutate 400`, with 0 differing.

## (d) the linter as built (`linter.rs`)

`linter.rs` ports `src/sany/linter.ts` on the modules the report parses, standard modules included, so it reads their texts' dummy definitions as SANY does.

1. **Records.** It collects each top-level module's records (record constructors and sets of records) in SANY's order of generation, with the names bound around each. That covers definitions, assumptions, theorems and their proofs (DEFINE steps included), and instance substitutions, but not inner modules.
2. **Exemption.** It exempts a record when a field of any record with the same fields (the module's own, or an extended module's) is built from declarations. Reaching a definition by name walks its body: in the defining module, and, through an INSTANCE of a module with declarations, also the instance's substitutions. That way `1 + 2` is built from the parameters of Naturals' `a+b == {a, b}`, while `2 * 3` (`a*b == TRUE`) isn't.
3. **Warning.** For a field named like a declaration or definition of the module, or of a module it extends, it writes SANY's warning at the field's name.

It returns `NotYet` for:

- a field named like an instance's definition, a theorem or an assumption;
- a subexpression it would have to follow.

`sany-text` reports 2,257 of 2,357 matching, and 2,558 of 3,957 with `--mutate 400`, with 0 differing. The corpora's 30 specs with linter warnings all match.

What's left `NotYet`:

| Specs | Cause |
|---|---|
| 89 | SANY's parse errors (`src/sany/parse-error.ts`) |
| 10 | Errors that stop linking |
| 1 | RECURSIVE arity |

## The startup section and operator tables as built

- `lower.rs` writes `model.startup` in the speed session's layout: the substitutes TLC checks, the constant definitions with effects in TLC's order, and the assumptions that aren't axioms with their names. This is `getIrStartup`, which `check.ts` now exports, so the model-full gate's TypeScript side writes the same section.
- SYMMETRY stays `NotYet` until its permuted sets are lowered.
- `create_environment` still returns `NotYet` for a substitute that isn't of constant level. The TypeScript environment evaluates it while linking, where the engine evaluates it at startup, so the two would differ on a substitute that fails (etest7, TLCGetNamedUndefined).
- A configuration's operator table (`F(0) = 1`) gives the environment's builtin its rows. `lower.rs` writes them with `Builtin::TABLE`, each row's arguments as a tuple.
- model-full: 831 of 1,111 with 0 differing, and 2,336 of 2,711 with `--mutate 400`.
