# Which definitions TLC computes at startup

Sources: TLC d8fb231 (SpecProcessor.processSpec, processConstants, processConstantDefns,
processModuleOverrides, processModelConstraints; SymbolNodeValueLookupProvider.getLevelBound), and
the notes from the liveness-atoms and fingerprint sessions.

## The single decision

For each definition, once the cfg is applied, TLC holds two separate facts. Every reader needs one
of them, and today each reader works them out again:

- **Read**: what evaluating the name gives. One of:
  - **Held(v)**: one value, computed or given before the search;
  - **Lazy**: the body, evaluated at each read in that read's state;
  - **Decline(reason)**: the value comes from Java we don't run (`processModuleOverrides`).
- **Defns**: what `defns.get(name)` holds, Value or Operator. The cfg-facing checks read this:
  - `getAliasSpec` and `getPostConditionSpecs` reject a Value ("cannot be a constant");
  - `processModelConstraints` drops a name only where `defns(name)` is TRUE;
  - `getConstantValue` evaluates the cfg's predicates.

The two facts differ exactly where the branches have accreted rules:

- **Literal body** (fingerprint's LITERAL): `processConstants` gives the literal a tool object, so
  `lookup(D)` gives the value and Read is Held. `processConstantDefns` then skips D because it isn't
  an OpDefNode, so Defns stays Operator. That is why `ALIAS D` is accepted.
- **Substitute for a declared constant, `C <- D`**: the first loop of `processConstantDefns` sets
  D's tool object, so Read is Held at any level. It never does `defns.put`, so Defns stays Operator
  (round 15's s3: TLC accepts `ALIAS D`).
- **Substitute for a definition, `X <- D`**: the second loop reaches D through X's tool object,
  evaluates it, and does `defns.put`, so both facts become Value.
- **A substitute the cfg also gives a value, `C <- D` or `X <- D` with `D = v`**: `processConstants`
  puts v in `defns(D)`, and the substitution copies that value to C's or X's tool object, so neither
  loop of `processConstantDefns` reaches D's body. D is not attempted.
- **0-ary OpDefNode of a module with `processConstantDefns()`** (not instantiated with parameters),
  not given a value by the cfg and not vetoed: TLC evaluates it if `getLevelBound(body) == 0`, and
  both facts become Value. `getLevelBound` differs from SANY's level in several ways:
  - an operator argument (a LAMBDA, or an operator passed by name) is level 0;
  - a name whose UniqueString has a varLoc is level 1;
  - builtins count at their Java `minLevel`;
  - a definition already Held counts as 0, so the processing order matters;
  - a LET counts every definition in it;
  - an INSTANCE substitution counts at its value's level.
- **INSTANCE copies with parameters** are never computed. Each `#n` copy is its own definition.
- **A computation that fails** is swallowed, and Read becomes Lazy. A failing `C <- D` with level
  bound above 0 instead stops the run with `TLC_CONFIG_SUBSTITUTION_NON_CONSTANT`.

Whether a definition is attempted is static. Whether the attempt succeeds is known only at startup.

## Where it is computed

- **Front end lowering**, after the cfg is bound, because only there are modules, copies, overrides
  and cfg seen together. It decides for each definition whether TLC attempts it, in what order, and
  under which rule. It also decides Defns, and decides Decline for Java overrides. It ports
  `getLevelBound` over the AST, including the varLoc rule.
- **Engine startup** evaluates every attempted definition once, in that order, with no state, and
  keeps the results in one table that the workers and tla-trace share:
  - a variable read fails as TLC's does;
  - `TLCGet("level")` reads the startup level;
  - a lazy value built at startup applies its body later with no state, as `FcnLambdaValue` does
    over `TLCState.Empty`;
  - the result is deep-normalized;
  - a failure makes Read Lazy.
- **tla-trace** reads the IR and that table. It asks no level questions of its own.

## The IR

- `startup.attempted: Vec<Attempt>`, in TLC's order:
  `Attempt { definition, rule: Substitute{constant} | DefinitionSubstitute | Constant }`.
- A per-definition two-bit field for the static part of Read (Held literal / Attempted / Lazy /
  Decline) and one bit for Defns.

These replace `Definition::NORMALIZED`, `startup.substitutes` and `startup.definitions`, and the
proposed `READ_DECLINED`, `LITERAL` and `UNPROCESSED`. The IR version goes up.

## Rules it replaces

- **tla-trace:**
  - `is_precomputed`;
  - `may_reach_bound`, with its LAMBDA, by-name, substitute and varLoc rules (my unmerged
    getVarLoc branch included);
  - the `captures` rule;
  - `Rebuilder::is_computed_at_startup`, now a read of Defns.
- **Engine:**
  - the lazy bail in `compile_startup_definition`;
  - `once` computing a definition at its first use, in that use's state.
- **Front end:**
  - `NORMALIZED`, which comes from SANY's level;
  - `is_held_literal`;
  - the READ_DECLINED marking;
  - the TRUE-bound constraint rule, now a read of Defns.
- **The dropped action-constraint commits** (lazy substitutes through EXCEPT/LET, the substitute
  declines, the copy declines): the model now covers them.

## Order to land, each its own PR, gate and adversarial round

1. **Front end computes the decision and emits it beside the old flags.** No reader changes.
   Report every definition in the corpus and the tests where the new decision differs from
   `NORMALIZED`, LITERAL or READ_DECLINED. Each difference must be a known wrong output; record any
   new one. Gate: the engine-ir goldens and both differentials unchanged.
2. **tla-trace and the cfg-facing checks read Read and Defns.** Their own rules are deleted.
   Regression set: the trace-kept and startup-level fixtures, all of rounds 1-15, constant-alias's
   jar cases, and atoms' adv8 cases (a) and (c).
3. **The engine evaluates attempted definitions at startup with no state.** Regression set: m1-m7
   and l7 (now right), the 34 inputs from rounds 11-13 that matched before and must still match,
   atoms' case (b), and the engine-ir goldens. Depot benchmark before and after.
4. **Delete the old flags and lists.**

## Step 1, as built

`tla-front/src/startup.rs` computes the static part: `get_startup_model` gives each definition's
Read (Literal, Attempted or Operator), whether `defns` holds its computed value, and the
attempts in order with their rule. `front-dump startup` reports it against `NORMALIZED` over a
list of models; `tests/startup.rs` holds each rule on a small spec. Nothing reads it yet.

TLC reads an operator a Java method overrides through the method, of the method's `minLevel`, and
never walks its definition. `tla-front/src/tlc_overrides.tsv` lists them, as
`scripts/tlc-overrides/TlcOverrides.java` reads them from the jar by reflection: the public static
methods of the `tlc2.module` classes named after a module (by `TLARegistry.mapName`), and every
`@TLAPlusOperator` and `@Evaluation`, CommunityModules' in `tlc2.overrides` among them. Those of a
level above constant are TLCGet, CounterExample, Trace, PickSuccessor, `_Counts`, `_TLCState`, and
IOUtils' IOExec, IOEnvExec and their templates. TLC sets a method on the body of the operator the
module of its class defines, so an operator of another module spelled the same keeps its own
body. A standard module's operator with no Java method TLC reads through its TLA+ definition, which
the model walks in the module's own text: Bags' SubBag binds x, y, f, i, r and s. Only the root
module's variables give a name a location, so only their spelling makes a name state-level; an
argument in the place of a parameter that takes arguments is an `OpArgNode`, of level 0 whatever
its spelling; and a theorem's or an assumption's name looks up to a `ThmOrAssumpDefNode`, whose
statement `getLevelBound` never enters.

Over the corpus (733 models) every difference from `NORMALIZED` is of a kind the model explains:
192 literal bodies and 155 substitutes for constants, where only Defns differs, and 23 definitions
TLC attempts that the front end marks state-level for their Java builtins (the trace specs' JSON
reads, RandomSubset) or for an action inside an operator argument (an attempt that fails). Over
the adversarial rounds of `design/trace.md` (914 models), the differences are the operator-argument
and TLCSet shapes of rounds 10 to 13 (116, attempted where `NORMALIZED` isn't), which give main's
wrong verdicts, and the names spelled as variables of rounds 14 to 16 (96, operators where
`NORMALIZED` is). Over the ALIAS review rounds (`cases-alias`, 1247 models, 114 of which TLC rejects),
the differences are 252 literal bodies and 20 substitutes for constants, where only Defns differs.

Still approximate: the order of the attempts is the substitutes, then the definitions in
`startup_definitions`' order, where TLC goes module by module with each module's substitutes
before its definitions; and a definition another one reaches counts as computed only by its own
level, where TLC counts a held value as level 0 whether or not it reaches the state.

## A startup definition that fails

TLC swallows what a constant definition throws as it starts and keeps the definition as an
operator, which it evaluates again, and fails again, wherever it is used (`processConstantDefns`).
The engine did the same for none: a failure declined the model.

Now `run_startup` goes on past a startup definition that fails with a failure TLC reports (not
one of the engine's limits) before any effect: nothing printed, no draw from the generator, no
register set (`evaluate_retried`). It must also be one TLC evaluates again at each use as the
engine does at the use (`is_retried_at_use`). That is an operator without parameters whose body,
through the definitions it names, doesn't read the state. It has no value TLC may keep lazy, and
no builtin whose value depends on when or how often TLC evaluates it, except Print, PrintT,
AssertEq, RandomElement, RandomSubset and TLCSet, whose effects the search sees run. Such a
definition fails at each use exactly as it failed at startup, before the same lack of effects, as
in `PrintT(<<expression that fails>>)`. Its `once` keeps no value, so each use evaluates the body.

The startup values hand on `NO_VALUE` for it. The trace evaluator takes that as a definition to
evaluate again where it is used, and so does a failure's evaluation, which takes those markers
even where it takes no other startup value. The trace evaluator does the same for one its own
startup finds failing before it printed, drew or set a register.

The engine retries only a failure TLC surely has where the engine has it. It does not retry the
ones its assumptions already leave to the trace evaluator (`UNSURE_FAILURES`), where TLC may
never test the set the engine finds failing.

At a use, the trace evaluator holds the definition to failing again as TLC does
(`evaluate_failed_startup`). Several cases decline instead:
- an evaluation that succeeds;
- an EXCEPT of a key outside the domain, which TLC warns of with 2144;
- an evaluation that built a set TLC can't normalize, or a value TLC may keep lazy;
- a failure in a function constructor, a filter or a map;
- a failure comparing, enumerating or testing membership.

TLC holds values unnormalized or lazy where the evaluator doesn't always, so in those cases it may
fail elsewhere: building its message, or at another element (fallback.md, "Known wrong outputs").
A set applied as a function declines before its argument is evaluated, as TLC fails there first,
naming the class it built the set as.

The engine prints only where it evaluates as TLC does, and declines a print elsewhere, as an
argument of most operators. So an effect TLC runs before the failure is one the engine runs
before it, which keeps the definition declining.

The native checker allows it only where the configuration scopes no substitute or value to a
module (`<- [M]`, `= [M]`), which the front end leaves out where TLC applies it; a model whose
startup failed would then read past it what TLC doesn't (fallback.md, "Known wrong outputs").
The interpreter's route and the simulation keep declining.

A failing definition that printed, drew or set a register before it failed still declines. So do
one that reads the state, TLC's search or the time, and one TLC keeps lazy (`may_be_lazy`, "a
value TLC computed at startup with effects"). So does an INSTANCE's copy with substitutions, or a
definition that names one. Its substitute may fail, and the trace leaves out the frames TLC
reports for a failing substitute (fallback.md, "A failing INSTANCE substitute").

## Asks

- **constant-alias:** land LITERAL as it is. Step 2 then folds it into Defns.
- **atoms:** send the adv8 and rerun cases as files once step 1 starts.
- **front-constants (#292):** READ_DECLINED stays until step 2.
