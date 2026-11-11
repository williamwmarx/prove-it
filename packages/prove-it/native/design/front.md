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
  `parse_module_tokens`, `parse_sany_module`) and `extractModule`. A module named by a
  keyword makes `parser.ts` run SANY's own parser (`getSanyParseError`), which F5 ports; until then
  the Rust parser returns an `unsupported:` error there in these modes, and no corpus module
  reaches it.
- The prover's stage P5a adds the `tlapm` mode (`parse_tlapm_module`): every `isTlapm` branch of
  `parser.ts`, behind `Mode::Tlapm`, with the lexer untouched. `@` stays an operator token, a
  string is located at its closing quote, `TRUE`, `FALSE`, `BOOLEAN`, `STRING` and the keywords
  are only keywords, brackets lift the junction list's alignment, `LAMBDA` is an expression, a
  prefix operator argument or a `\B`, `\O` or `\H` numeral is an `incomplete expression`,
  `RECURSIVE` inside `LET` is rejected, `DEF` takes tlapm's definables, and SANY's precedence and
  label fix-ups are skipped. A failure carries the reason and position tlapm prints: `Unexpected
  EOF` after the unit's `==`, or `Unexpected <token>` at the end of the token before it. The
  Rust-only readings the checker relies on (a fairness subscript applied to arguments) stay out of
  this mode, and a keyword module name runs the ported `get_sany_parse_error` as `parser.ts` does.
  `front-differential.ts tlapm-ast` compares the AST, or the error and its failure, with
  `parseTlapmModule`: all 2,367 modules match (the corpora, with the 304 modules of `proofs.json`
  and the error corpus of `tlapm.json`, and the fixtures), and so do the 9,468 variants of
  `--mutate 2400`.
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

## The constant evaluator as built (`eval.rs`)

`eval::Evaluator` evaluates the constant expressions the front end needs values of before the search, as `evaluate.ts` computes them:

- booleans, integers, strings, model values, and finite sets of them, normalized in TLC's order (`values::ValueOrder`, by the texts' ranks);
- configuration constants, substitutions, definitions and closures, and LET;
- the arithmetic, comparison and set operators of Naturals, Integers and FiniteSets, and membership in Nat, Int and STRING;
- junctions, IF, quantifiers, set filters and set maps.

Anything else is `NotYet`: tuples, records, functions, CHOOSE, SUBSET, TLC 1.7.4's streamed sets, and every evaluation error, which TLC's startup reports.

`get_bindings` binds a list of bounds to their sets' elements in `forEachBoundElement`'s order, the last bound outermost.

A property's `\A` over constant sets is now unrolled, as `expandTemporal` does for properties, with each instance named by `describeRange` of the body. A `\A` over sets that aren't constant stays a single formula, as in TypeScript.

model-full: 842 of 1,111 with 0 differing, and 2,355 of 2,711 with `--mutate 400`.

The liveness session wires the evaluator into `live.rs`: the temporal quantifiers over constant sets, the constant parts and the constant IF conditions.

## SYMMETRY in the startup section

`lower.rs` writes the SYMMETRY entry of `model.startup` as `getIrStartup` does: the definition, then `getPermutedSets` of its body. That is each argument the body's operator applies to, named by the configuration's substitution for its image or by the image (`getHumanReadableImage`, over the resolved keys as TypeScript's AST holds them). For `Permutations(S)` of an identifier the configuration doesn't replace with `<-`, it also writes S. The engine evaluates the group. model-full: 918 of 1,111 with 0 differing, and 2,441 of 2,711 with `--mutate 400`.

## A spec without variables

TLC searches no states of a spec without variables. `check.ts` lowers its model, once
`createSearch`'s configuration checks pass, with the identifier `FALSE` at (0,0) as both the
initial predicate and the next-state relation, no properties, no liveness and an empty TLC order,
but with the startup section, so the binary still evaluates its assumptions and finds no initial
state. `lower_model` does the same; the configuration errors of such a spec stay not yet. The
TS side is `lowerConstantSpec`, which both the dump path and the model-full gate call.

## Substitutes TLC evaluates at startup

TLC evaluates a parameterless substitute for a declared constant at startup and rejects it only
when that fails and the level bound `createLevelAnalyzer` computes is above constant, with TLCGet,
Trace and CounterExample read as variables. `create_environment` runs the same analyzer from
`levels.rs`, and evaluates such a substitute with the constant evaluator before TLC starts
(`is_started: false`, with no string ranks). Two failures are TLC's:

- a variable, which no state assigns: TLC's "is either undefined or not an operator";
- TLCGet of a key TLC's model checker holds (diameter, generated, distinct, queue, stats, config),
  which `TLCGetSet.TLCGetEval` reports as its own failure on master.

Either becomes TLC's configuration error "substitutes constant C with non-constant D -
specifically: …". Anything else the evaluator can't compute is still `NotYet`.

## Constant parts of the liveness formula

`live.rs` evaluates what `toLiveExpression` evaluates, with the constant evaluator:

- a constant atom becomes TRUE or FALSE;
- a quantifier whose bound sets are all constant is expanded over their bindings, in the order
  `get_bindings` gives them, into a conjunction or disjunction of the body's conversions, or
  TRUE or FALSE over no bindings;
- an IF whose condition is a constant boolean converts only the branch it chooses.

Where the evaluator fails, TLC's handling (an atom, or "cannot handle" with the failure's message)
isn't followed yet, so it stays `NotYet`, as does a constant atom that isn't a boolean.

## The configuration checks of `createSearch`

`lower_model` makes `createSearch`'s checks in its order:

1. Each invariant is a state predicate by SANY's level analysis (`check_invariants`, before the
   specification). `Environment` keeps the resolution tables, and `create_level_analyzer` builds
   the analyzer the startup substitutes use too.
2. The specification and its properties.
3. A missing initial predicate, then a missing next-state relation.
4. `check_search_config`: the constraints, action constraints, RL reward, periodic and possible
   operators, and, with variables, the SYMMETRY's definition and the VIEW.

`getConstantValue` evaluates a constant definition the configuration names with the constant
evaluator. A value other than TRUE is TLC's configuration error, and a definition that fails to
evaluate stays an operator, as in TLC. The engine checks the same definitions again at startup
(`Startup::predicates`, below), so a predicate the evaluator can't compute yet is left to it:
the evaluator records the deferral, and any error the front end would report after it becomes
`NotYet`, since TLC stops on the predicate first. TLC rejects any value of an INIT, NEXT, possible
or SPECIFICATION definition, so one of those the evaluator can't compute stays `NotYet`. The evaluator reads
the builtins the configuration substitutes (`Nat <- Int`), and stops as `NotYet` past 400 nested
evaluations rather than overflow on a recursion.

A text with a lone surrogate, which TLC's strings hold, makes the TypeScript IR decline the
model; model-full lists such a model as not compared.

## TLC's errors of the specification and its temporal formulas

`get_specification` and `get_properties` read a conjunct that is a constant name as
`isConstantTrue` does, with the evaluator: TRUE is dropped, FALSE is "The spec is trivially
false", and another value can't be "used as a spec". `[]P` of a state predicate in the
specification is "TLC cannot handle the temporal formula" at P.
TLC takes a state predicate a LET defines whole, as it does a definition's, so a constant conjunct
inside one is no conjunct of the specification; the front end, which expands the LET's
conjuncts, drops one that is TRUE, as TLC's predicate would hold it, and declines another.

`live.rs` follows `toLiveExpression`'s failures:
- "cannot handle" at a formula it can't translate;
- `expandCall` re-reports a failure inside an operator's expansion as "cannot handle" at the
  application, except for a recursive operator;
- a constant quantifier whose body fails becomes an atom below temporal level, or "cannot handle"
  under `\E` (under `\A`, TLC adds the inner message: still `NotYet`);
- expanding past 100 levels is TLC's stack overflow.

`tla_live::atom_order`'s refusals become TLC's errors: the tautology, the formula too large in
disjunctive normal form, and actions outside `<>[]A` and `[]<>A`.

## Startup predicates and normalized definitions

`Startup::predicates` lists each constant-level definition the configuration names, unless it is a
literal number or string or a constant the configuration assigns, in TLC's order:
invariants, the SPECIFICATION or INIT and NEXT, properties, constraints, action constraints,
then possible (`getConstantPredicates` in `search.ts`). Each entry carries how TLC rejects the
value: a predicate for any value but TRUE, a definition and the SPECIFICATION for any value. The
engine evaluates them after the constant definitions and before the SYMMETRY and the
assumptions, and swallows a failure to evaluate, as `getConstantValue` does.

`Definition::NORMALIZED` marks each definition TLC computes and deep-normalizes in
`processConstantDefns`: `isStartupDefinition` over the startup definitions, which skip the
modules an INSTANCE gives parameters to.

## Models without a next-state relation, and properties in a scope

`Model::next` is optional: TLC computes the initial states of a model whose configuration names
no next-state relation (and checks nothing of behaviors), then stops. `check.ts` lowers it, and a
spec without variables, through `lowerUnsearchedSpec`.

Each property invariant, action property and initial predicate carries the scope of the instance
it comes from (`property_invariant_scopes`, `ActionProperty::scope`,
`initial_predicate_scopes`), which `Model::has_scoped_property` tells; the engine and tla-trace
decline one until they read it there. An operator argument to a temporal formula binds a closure as
`evaluateOperatorArgument` does: a LAMBDA, a local operator, or a definition, and an application of
an instance's operator is named by its key, as TLC names the property it checks.

## TLC's failures the evaluator raises as they are

The evaluator computes CASE, CHOOSE over a set it lists, and, for what it can't hold (DOMAIN, a
record's field), the argument first, as TLC does, so a failure there comes out as TLC's. A
quantifier or CHOOSE over `[D -> R]` with D a set TLC knows only by name (Nat, Int, STRING) fails
as `enumerateSet` does, which IOUtils' `IOEnv` meets without its Java override. `live.rs` raises
such a failure of a constant part as `toAtom` does, and `expandCall` still re-reports one inside an
operator's expansion as "cannot handle".

## Records in the constant evaluator

`ConfigValue::Record` holds a record the evaluator builds, its fields sorted by TLC's string order
of their names (`getSortedFields`). The evaluator computes record constructors, sets of records
(the last field varying fastest, as `getCartesianProduct` lists them, then sorted) and field
selection. `ValueOrder::compare` orders two records as `compareFunctions` does: by size, then names
by rank, then values. The lowering writes one as TLC's RecordValue (function class 3, the names
before the values). A repeated field, a missing field, a field of another value, TLC 1.7.4's sets
of records, and tuples and other functions stay `NotYet`.

`ir.ts` writes a name that nothing global resolves (a definition an INSTANCE in a LET copies in)
with the local flag; `lower.rs` does the same.

## Handoff

model-full: 1,100 of 1,111 with 0 differing, and 2,695 of 2,711 with `--mutate 400`. The 11 not
compared:

| Models | Cause |
|---|---|
| 10 | SANY's parse errors: TLC itself fails to parse these specs ("Precedence conflict" in ccfraft, KVsnap, Linearizability, Bodega, NormalizationCases, and the two fixtures' `Base`), so no model is lowered. The native binary's SANY report owns their output. |
| 1 | `tlc-174/Unhandled`, TLC 1.7.4 only. |

## The binary's front (tla-front alone)

`front.rs` reads the whole front from tla-front, the binary's only front end since the recorded
front was removed: `Front` holds SANY's report and `LoweredModel::startup_messages`,
what TLC prints itself after the constant definitions and before the assumptions, in its order:

- 2149, each invariant that is a constant equal to TRUE (`check_invariants`), and 2255, each
  property that is a state formula, both warnings, which `-nowarning` drops;
- with liveness, 2279 under a SYMMETRY (a warning), then 2212 "Implied-temporal
  checking--satisfiability problem has N branches.", N counted by `tla_live::count_branches`.

The CLI prints SANY's report framed under -tool, then 2185 `Starting...`, and, through the engine's
startup hooks, what Print and PrintT print as TLC starts and the symmetry's 2300, and
`startup_messages` at `startup_done`. Not native yet in tla-front: TLC 1.7.4, an invariant the
engine checks at startup with warnings on, and warnings about invariants or properties under a
SYMMETRY (the order of 2300 among them isn't checked).

`java_overrides` ports `java-overrides.ts`: the public static methods of the class named after a
module, beside the spec (`EnvironmentOptions::load_class`, which `lower_model` gives), replace the
operators of the same name and arity with the constant they return (`BoolValue.ValTrue`,
`IntValue.gen(n)`, `new StringValue(s)`). `LoweredModel::override_messages` is TLC's 2168 for each
(2400, a warning, for a method that matches no operator), which the binary prints right after
`Starting...`. Not native: a method that computes its value, a method with parameters (TLC evaluates each
argument, in order, before it calls the method, `OpValue.eval`, so an argument that fails or prints
does so, which the literal would skip; both fronts decline it), overrides of two modules, a class
path a URL would escape, and more than one report, which TLC lists in the JVM's order.

Both fronts read an override class only within a whitelist, since Java runs what a class holds
around the method TLC calls; outside it they decline, naming why (`tests/fixtures/override-shapes`
holds a class for each exclusion, with what TLC does with it):

- a class file of version 69 or older whose constant pool holds only the JVM's known tags;
- a plain class (not an interface, abstract, annotation, enum or module) that extends
  java.lang.Object, implements no interface, and has no fields and no static initializer, which
  TLC runs as it first calls an override;
- no annotations, such as `@TLAPlusOperator`, whose method TLC skips here;
- one public static method of each name, none a name TLC maps to an operator's
  (`TLARegistry.mapName`, such as `Plus` for `+`);
- a matched method without parameters whose bytecode is one of `getstatic BoolValue.ValTrue` or
  `ValFalse`, an int constant then `invokestatic IntValue.gen(I)`, or `new StringValue`, `dup`, a
  string constant and `invokespecial StringValue.<init>(String)`, then `areturn` as its last
  instruction, with no exception table.

The binary prints an assumption's Print of a value the store can't word as the trace evaluator
prints it (`Rebuilder::check_assumption`, each assumption in turn), as 635457c does for the
startup's, as long as every print before it the store worded alike.

`ModelOptions::random_seed` carries `-seed` into the model, as `runtime.seed` does.

`bun scripts/run.ts differential --native native/target/release/prove-it --native-only` runs the
binary alone this way, without the TypeScript runs, on the whole corpus,
against TLC's recordings, in minutes. Measured before the hooks were wired, with `check.rs` printing
the messages after `Starting...` and no startup Prints: 1,298 of 1,466 runs printed what TLC prints,
and the 80 that differed each lacked a startup Print, which the hooks now report.

No-recording mode on the whole corpus (`--native-only`, after the messages landed): 1,392 of 1,466
runs print what TLC prints and none differ. Of the 74 others, 4 are listed known differences
(function_syntax, where TLC overflows its stack) and 2 decline for a Java class that overrides a
module, the front end's one open case; the rest are the engine's and the trace evaluator's
declines, as with a recorded front.

A property is named by its operator as written (`opNode.getName()`): `PSafe == A!Safe` names
"A!Safe", while `A!Safe2 == Safe` inside the instance names "Safe". `expand` takes the identifier's
written name; the TypeScript resolver keeps it in `getWrittenName` (`tests/fixtures/instance-property`).

After the overrides and the assumptions' prints: 1,400 of 1,466 runs in no-recording mode, none
differing, against 1,402 with recordings. The 2 runs only a recording gives are
test-model/CyclicRedefineInstance, whose Next `tla_trace::add_actions` can't split through an
INSTANCE in a LET; the recorded IR holds the TypeScript front end's actions.

## SANY's check of a recursive operator's arguments

`levels.rs` ports `src/levels.ts`, which lacks the check `ModuleNode.levelCheck` makes of each
recursive section (`src/sany/levels.ts`, which the TypeScript CLI's report runs): a RECURSIVE
operator, of the module or of a LET, whose body takes an argument below action level, as a primed
parameter, is "Argument i of recursive operator Op is primed" at the definition. A unit at the
module's start reports it, before the module's other units, as SANY checks the recursive sections
first. `NotYet`: a recursive operator that applies another (SANY's first pass reads the section's
operators with action-level arguments), one whose levels fail to analyze, and errors of both a
module's and a LET's operators, whose order isn't checked.

## TLC's negative tests

`tlatools/test/tla2sany/semantic/error_corpus` (125 specs, each a SANY error) and `corpus` (28
specs SANY accepts), run through the binary against master TLC with an empty configuration: 116
and 21 print what TLC prints, and the rest decline. None differ. The front end's checks they
brought:

- `resolve.rs`: SANY's `@` outside an EXCEPT, a recursive section's units, a function's RECURSIVE
  declaration with parameters, a function applied to another number of arguments, the arity of an
  explicit substitute (two errors, the second in `--TLA+ BUILTINS--`), and DEF entries that aren't
  definitions.
- `levels.rs`: an assumption above level 0, `checkArguments`'s errors of an operator's
  arguments, junctions' and bounded quantifiers' level errors under SANY's names, and a NEW over a
  temporal set.
- The parser: a named `<*>` or `<+>` step, a semantic error of the TLC-mode parse, and SANY's
  `WF_B(A)(Act)`, whose subscript is `B(A)`.
- `report.rs` declines a module the front end's parser rejects where SANY's parser
  (`sany_parse_error`) accepts it, rather than print the front end's message.
- `get_coded` reports a decimal or an integer TLC can't hold as SpecProcessor does: 2244 or 2265,
  the literal on its own line, exit 151 or 255. The TypeScript CLI still prints the front end's
  error (code 1000, exit 75).

The generator's checks the error corpus declined (E4200, E4203, E4204, E4223, E4293 ×2, E4294,
E4351, E4355) are now written, from `Generator.java` and `SymbolTable.java` at d8fb231:

- `selectorToNode` (`resolve.rs`, `get_symbol_arity`): an INSTANCE's name as an expression, with
  its arguments checked first ("The operator I requires n arguments." at the arguments, or at the
  name without any) and then "Operator name I is incomplete." at the name; in a fact SANY takes the
  name, which stays `NotYet`. A theorem whose statement is an ASSUME/PROVE, and a step whose name
  `Local::unselectable` marks: "ASSUME/PROVE used where an expression is required." for an
  ASSUME/PROVE step, and "HAVE", "CASE", "TAKE", "PICK", "WITNESS", "QED step" or "SUFFICES"
  "proof step selected instead of expression." A theorem whose statement is an expression, which
  SANY takes as one, is linked as a definition, which its own proof may name too (below).
- RECURSIVE declarations: `recursive.rs` names the shapes the front end follows, and every other
  module with a RECURSIVE declaration is `NotYet`. `processRecursive` binds each declared operator
  at the current LET/IN level (`curLevel`), `processOperator` and `processFunction` define it,
  `checkForUndefinedRecursiveOps` reports it at the end of its LET or module if nothing has, and
  `SymbolTable.addSymbol` decides what any other binding of its name means. The front end follows
  a declaration of N with k arguments, at module level or in a LET, only where N is no built-in,
  nothing before it in its module or LET names or binds N, and nothing after it in its scope binds
  N but one definition of N in the same module or LET (or, for a LET, one LET definition of N
  within a later definition of that LET, "defined at wrong LET/IN level"). That definition is an
  operator with k parameters that take no arguments, or a function when k is 0; at module level it
  may instead have another number of such parameters ("Definition of N has different arity than its
  RECURSIVE declaration.") or be a function when k isn't 0 ("Function N has operator arguments in
  its RECURSIVE declaration."). Where N is left undefined, defined at a deeper LET, or defined in
  one of those two other shapes, nothing may name N. A LET with RECURSIVE declarations has no
  INSTANCE and no other such LET within it; a nested module declares nothing RECURSIVE at its own
  level; no INSTANCE without a name follows a module-level declaration; and the resolver declines
  a declaration of a name already bound where it appears. Within these, a LET's declarations are
  in the AST (`ExpressionKind::Let::recursive`) and bind as pending operators with the
  declaration's arity, and at the end of the LET's definitions, before its body, which is a level
  up, SANY reports "Symbol S declared in RECURSIVE statement but not defined." for every
  declaration of that level it has read and left undefined (`recursiveDecls` is the module's),
  each once, as `Errors.addMessage` drops a message it holds.
  `crates/tla-front/tests/recursive-shapes` holds a grid of declarations at module level, in a LET
  and in a LET within a definition of another, against everything else that can bind or name what
  they declare; the `report.rs` test lists the cells the front end reports, and
  `scripts/sany-corpus.ts --specs` runs the grid through TLC. The grid isn't among the fixtures
  `front-differential.ts` reads, as the TypeScript resolver doesn't follow these declarations.
- `generateUseOrHide` and `generateLeafProof`: the parser keeps every DEF entry in the SANY run,
  and `check_defs` reports, where SANY meets it, an unknown name ("Unknown operator: `X'." then
  "DEF clause entry should describe a defined operator.") and a built-in operator, a constant, a
  variable, a parameter or a NEW symbol (the second only). A USE or HIDE that keeps no fact and no
  entry is "Empty USE or HIDE statement.", and such a BY "Empty BY".
- `SymbolTable.addModule`: a nested module named like a standard module SANY has read is
  "Multiply-defined module", at the standard module's extent, which `get_standard_source` reads
  from SANY's text of it; where the module has other errors, whose order with it isn't followed,
  `NotYet`.
- `SimpleFilenameToStream.locate` reads a user's file, then a standard module, and only then
  (`FileUtil`) a module of the root module's file, so `report.rs` reads a standard module before a
  nested module of its name, which SANY's parse doesn't see.

- E4294_Module, a MODULE inside a recursive section: the nested module's end takes the section's
  count off the total (`checkForUndefinedRecursiveOps`), so the definition after it drives the
  total below zero and `endOpDefNode` throws a WrongInvocationException. `SANY.parse` prints it
  after the module's "Semantic processing" line and none of its messages, and SpecProcessor fails
  with `Assert.fail(EC.TLC_PARSING_FAILED2, e)`, whose message TLC words with 2171 twice (nested
  markers under -tool), with no "SANY finished." or "Starting...", and exit 150; recorded from TLC
  at d8fb231 (`report.rs` `get_generator_exception`, `SanyText::exception`). It is written for
  the root module after standard modules alone; a recursive section the module leaves without a
  definition after it, or one that goes on after it, stays `NotYet`. The TypeScript report's "A
  MODULE may not appear within a recursive definition section." is not what TLC does.

- `processTheorem` adds a theorem whose statement is an expression to the symbol table before its
  proof, so `resolve_theorem` reads the proof after the theorem's definition, and the proof may
  name the theorem as an expression (ProofsTest's `DefineStepProof`).
- `Tool.isValid` fails on an assumption that is no boolean with "TLC expected a boolean value, but
  did not find one." and the assumption's place (EC 2215), which `checkAssumptions` reports within
  2105; `tla-trace` replays it so (AssumeTest, BasicTest, InnerModuleTest and Semantics, whose
  `ASSUME RefersTo(...)` is a string).

Declines left, each for a reason:

- The RECURSIVE grid's 7 specs that decline in the check stage's linking (`resolve.rs`):
  RLetInnerRecursive, RLetInstanceAfter, RLetInstanceBefore, RModuleInstanceUnnamed,
  RModuleModuleDeclares, RNestedInnerRecursive and RNestedInstanceAfter. SANY's report of each is
  written: where linking declines, `sany/messages.rs` takes SANY's messages from the ported
  generator, and declines any message whose shape no recording in `grid.json` or `corpus.json`
  shows.

The binary names the check it declines (`SANY's report of <reason>`).

`bun scripts/sany-corpus.ts --tlaplus <clone> --classpath <tla2tools>` runs TLC live against the
binary over both directories and counts them (TLC runs on the coordinator's side, as this
container can't build it). Before the port 138 of 153 printed what TLC prints (116 of the 125
errors, 22 of the 28 accepted specs), 15 declined and none differed; after it, before E4294_Module
was written, 146 printed, 7 declined and none differed: all 125 errors but E4294_Module, and the
six accepted specs above. `front-differential.ts sany-text` stays at 2,367 of 2,367.

### Open

- `report.rs`'s semantic checks still port `src/resolve.ts` and `src/levels.ts`, not the whole of
  `src/sany`; the generator's errors the corpus doesn't reach are the next to port.
- A RECURSIVE operator that applies another of its section (mutual recursion): SANY's first pass
  reads the section's operators with action-level arguments, which `levels.rs` declines.
- The TypeScript front end's differences from TLC, below.

### Where the TypeScript front end differs from TLC

The TypeScript CLI's report still differs from TLC on these, which the native front writes or
declines:

- E4243 ×3 (an explicit substitute's arity, two errors in SANY) and E4260 ×2 (a function applied
  to another number of arguments).
- E4294_Module (an exception, above) and E4350_Plus/Star (a named `<*>` or `<+>` step, which it
  rejects as a parse error).
- AssumeProveTest (a labeled ASSUME/PROVE among the assumptions) and FairnessTest (`WF_B(A)(Act)`),
  which it rejects as parse errors.
- NumbersTest: a decimal or a number TLC can't hold, which it reports with code 1000 and exit 75
  for TLC's 2244 (exit 151) and 2265 (exit 255).
- ProofsTest (a theorem named as an expression in its own proof), which the native front writes.
- LetInTest, and an INSTANCE named as a fact, which it reports as unknown operators.

## The strings TLC interns as it starts

TLC orders strings and model values by when it interns their texts, and it interns those
ToString, `\o`, Tail and SubSeq make as it computes the constant definitions
(`processConstantDefns`). `check.ts` lowers its IR after it has computed them, so a recorded IR
ranks them; `lower_front` ranks only the spec's. The binary lowers with `lower_front_ranking`:
`tla_trace::get_startup_texts` evaluates the substitutes and every startup definition the IR holds,
in TLC's order, ranking what those operators make as `rankString` does, and where it finds some, the
model is lowered again with them ranked (test-model/Github696, whose search compares `A_31` with
`B_a`). `lower_front` and the model-full gate keep the spec's ranks, as the TypeScript side of that
gate computes no startup.

No-recording mode on the whole corpus after it and after the split of a LET's operator
(test-model/CyclicRedefineInstance): 1,460 of 1,466 runs print what TLC prints, and the 6 others
are listed known differences.

## Retiring the TypeScript SANY front end (`src/sany`)

`src/sany` (about 12,000 lines) wrote SANY's report for the CLI of `dist/`, which never ran the
native binary, and the addon and the WebAssembly engine linked no tla-front. Nothing in the
prover, the obligations or the public API imports it. Its parts:

- The report itself (`report`, `generator`, `levels`, `linter`, `selectors`, `nodes`, `snapshot`):
  tla-front writes it byte-identically for TLC master, except where it declines.
- `xml`, SANY's XMLExporter: deleted once tla-front wrote it ("SANY's XMLExporter as built",
  below). The `generator`, `nodes`, `selectors`, `builtins` and `levels` it read stay with the
  report.
- What the TypeScript front end, and so the interpreter, reads besides: `parse-error` and `lexer`
  (its syntax errors and the configuration's), `modules` (the standard modules' texts, from which
  `scripts/front-modules.ts` writes tla-front's), and `source` (the readings `src/tlc/order.ts`
  takes). These move out of `src/sany` and stay until the interpreter is retired.

In three stages, each with TLC's recorded output as the gate in place of `sany-text`'s TypeScript
side:

1. tla-front in the addon and the WebAssembly engine (`prove-it-host`'s `sany`, `sanyText`), which
   the CLI calls (`src/cli/sany-text.ts`), keeping the TypeScript report where it declines.
   `scripts/sany-corpus.ts --recorded` holds the binary and the CLI to TLC's recorded output on
   SANY's corpus and on `tests/recursive-shapes`.
2. SANY's XMLExporter in tla-front, held to recordings of TLC's (done: `src/sany/xml.ts` is
   deleted, and the CLI exports through the engine).
3. `src/sany` deleted, with what the interpreter reads moved beside the TypeScript front end.
   `PROVE_IT_ENGINE=0` then needs the addon or the WebAssembly engine for SANY's report
   (fallback.md).

Before stage 3, tla-front also writes what the CLI still takes from the TypeScript report:
TLC 1.7.4's report, the trace exploration spec TLC parses with the spec where it writes one (TLC's
default without `-noGenerateSpecTE`, `-tool` or `-continue`; the binary declines it too), and the
exception of SANY's generator (E4294_Module), which the CLI's printer doesn't word yet.

`sanyText` reads nothing itself. It names what the report reads that it hasn't been given, a
module's text by its name or the file TLC prints that it parses a module from, and the CLI calls
it again with those, so the WebAssembly engine needs no file system and no call back into
JavaScript. The report is written again from the start each time, which costs a few milliseconds
for a few rounds. This is how every export of the host reads what JavaScript holds
(`prove-it-host`'s `sources`, which lists the keys): the in-process check and the prover's
exports read their sources this way too.

The report grows the WebAssembly engine from 1.39 MB to 2.98 MB, and the addon on x86_64 Linux
from 2.22 MB to 4.23 MB. One module carries it, as the in-process check will need tla-front's
parser, resolver and lowering there anyway. Of the addon's 2.0 MB, about 0.74 MB is the report's
alone (an addon with the report and the lowering is 5.35 MB, one with the lowering alone 4.61 MB),
and 1.27 MB the parser, resolver and level checks the lowering shares; in proportion, about
0.6 MB of the WebAssembly engine's 1.6 MB. That part could go behind a feature of the host crates
for a build without the CLI, which nothing builds yet.

On SANY's corpus (153 specs), the CLI with the addon prints what the binary prints on 144 specs,
up from 135. The 3 that differ are E4294_Module, which the CLI leaves to the TypeScript report,
and FairnessTest and NumbersTest, whose model the TypeScript front end rejects after SANY's
report. The other 6 decline in both.

Against TLC's output on d8fb231, recorded in `tests/conformance/sany-stdout`, the binary prints
what TLC prints on all 153 of the corpus's specs, and on 183 of the grid's 190, declining 7 in the
check stage's linking; none differ. Verification's Front End task holds it to that.
The CLI, with the addon, prints what TLC prints on the same 153 and 183, and declines the same 7
(`--cli`, measured at train-three 8695192d with `PROVE_IT_ENGINE_ADDON` naming the addon). Without
an engine it prints the TypeScript report, which differs on 17 of the corpus's specs and 7 of the
grid's. An npm install loads the platform package's addon or the WebAssembly engine `dist` ships.

The addon writes the report on a 64 MiB thread, as the binary's run does: a formula nested a few
hundred parentheses deep overflows the stack of the thread JavaScript calls on.

## SANY's XMLExporter as built (`sany/`)

tlapm and other tools read a module through `tla2sany.xml.XMLExporter`, which writes SANY's
semantic graph: every node with SANY's UID, the level SANY's levelCheck gives it, and a
definition's comments. tla-front's AST and resolution hold none of that, so `src/sany` ports the
TypeScript emulation of SANY's graph literally, file for file, over the Rust AST (which mirrors
`ast.ts`):

| Rust | TypeScript | What it holds |
|---|---|---|
| `sany/nodes.rs` | `sany/nodes.ts` | the graph, an arena of nodes addressed by `NodeId`, each with its UID (`Node::uid`, a counter apart from the arena: SANY numbers nodes the graph never holds, such as its first set of builtins); SANY's `Context`, a `java.util.Hashtable` that enumerates as OpenJDK does |
| `sany/source.rs` | `sany/source.ts` | token spans, the locations SANY gives what the AST leaves out, and pre-comments, sliced at each `(*` and `*)` as SANY's lexer ends a comment token |
| `sany/builtins.rs` | `sany/builtins.ts` | `BuiltInOperators`, with their levels; a variadic builtin has no `params` and SANY's arity -1 (`OpDef::get_sany_arity`) |
| `sany/selectors.rs` | `sany/selectors.ts` | `Generator.selectorToNode` |
| `sany/generator/` | `sany/generator.ts` | `Generator`: the module loader and SANY's order, the UIDs (two sets of builtins, InAssumeDummyNode, four null nodes per module), expressions (`expressions.rs`), definitions, substitutions and instances (`definitions.rs`), proofs (`proofs.rs`) |
| `sany/levels.rs` | `sany/levels.ts` | SANY's levelCheck of each node |
| `sany/xml.rs` | `sany/xml.ts` | the writer with `-r`, `-u`, `-t`; the context of symbols in the order of `java.util.HashMap<Integer>` |
| `sany/export.rs` | `cli/xml-exporter.ts` `exportXml` | the run: SANY's report, then the graph, level-checked, then the XML |

TLC 1.7.4's exporter is retired and not ported, nor is `snapshot.ts` (the build's cache of the
standard modules' graph): the Rust generates them on each run.

What SANY prints is `report.rs`'s, run as XMLExporter runs SANY (`ReportOptions::is_xml_export`:
no progress lines, no warnings, no PlusCal validation, no linting). The graph is built only for a
spec the report accepts, and an error of the generator the report didn't print is `NotYet`, so the
two can't disagree silently. Also `NotYet`: what XMLExporter prints with Java's stack traces (a
DEFINE step a DEF clause names, which it can't export, and SANY's generator exception of
E4294_Module), and a context whose HashMap would make a bucket a tree (9 UIDs in one bucket),
whose order neither port follows. `prove-it-check`'s `xml_exporter.rs` takes XMLExporter's
arguments and usage, and names a root module that no file holds as SimpleFilenameToStream does.

Gates, run by Verification's Front End job (until the TypeScript exporter was deleted,
`front-differential.ts sany-xml` also held the two exporters to each other on every module of the
corpora: 2,362 of 2,367 matched and none differed):

- `sany-corpus.ts --recorded` on `tests/conformance/sany-stdout/xml-*.json`, the real exporter at
  d8fb231: with each of the five flag sets, 151 of SANY's 153 corpus specs print what it printed
  and 2 decline (LetInTest, which the front end declines, and E4294_Module);
  8 of the 9 XML fixtures (DefineStep declines), and both `-I` fixtures. None differ. The
  TypeScript exporter printed what it printed on 142. Porting it found that the parser gave the
  subscript `B(A)` of `WF_B(A)(Act)` no range (FairnessTest), which SANY locates over its
  arguments.

Known approximation: `levels.rs` copies a source's level sets where `levels.ts` shares them
(`shareLevels`, for OpArg, Label, Assume and NewSymb nodes); the two differ only if the source's
sets grow after the copy, which no gate has shown.

### The CLI calls the native exporter

`prove-it-host`'s `sanyXml(root, source, fileName, flags, known)` runs `export_xml` on the
`Sources` convention (`module:<name>`, as `sanyText`), through the addon and the WebAssembly
engine (ABI 14). The JavaScript CLI's XMLExporter is native only: `src/sany/xml.ts` and TLC
1.7.4's exporter are deleted, and where tla-front declines, the CLI prints `prove-it: not native
yet: <reason>` and exits 1, as the binary does, and without an engine it fails as the CLI does
elsewhere. TLC 1.7.4's XMLExporter (`-cp` its jar, or `-Dtla-ts.tlc=1.7.4`) declines. The rest
of `src/sany` stays while the TypeScript report uses it (the CLI's fallback where tla-front
declines SANY's report, TLC 1.7.4's report); the front end's session retires it.
