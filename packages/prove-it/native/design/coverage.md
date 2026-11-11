# How the engine counts TLC's coverage

`-coverage` prints TLC's cost model (cli.md, "-coverage"): how often TLC's `Tool` evaluated each
`OpApplNode` of each action, invariant and constraint, and an estimate of how many values each
variable took. Two counters produce the same report, and the binary prints the engine's where the
engine counts the model, else the replay's:

- the replay (tla-trace `coverage/`): a port of TLC's `Tool` over SANY-shaped expressions, run
  after the search. It follows TLC node for node, and runs at about a quarter of TLC's speed.
- the counting variant of the engine's compiled code (tla-engine `compile/coverage.rs`,
  `compile/coverage_walk.rs`), which counts as the search runs.

Both count into one tree: `tla_engine::coverage::Tree`, the wrappers `CostModelCreator` builds,
which tla-trace builds (`Rebuilder::coverage_plan`) from SANY's view of the IR and hands the search
in `Settings::coverage` as a `Plan`, with the SANY node each IR node translates to and the roots.
The engine's counts come back through `Reporter::counted`, and tla-trace prints them with the
replay's printer (`Rebuilder::coverage_report`).

## Why the wrappers are fixed as the code compiles

TLC finds an expression's wrapper at run time, `CostModel.get(node)` under the wrapper of the
application it is evaluated in. The compiler expands each operator where it is applied, so each
closure it makes is of one path from a root: the wrapper each closure counts into is known as it
compiles, and the counting variant carries it in `Context::cm`. A lookup TLC would fail
(`TLC_COVERAGE_MISMATCH`) fails as it compiles, and the variant declines.

## What the variant changes

It is compiled only where a search asks for coverage; a search without `-coverage` compiles and
runs the code it always did. Where it is compiled:

- Each `OpApplNode` TLC's `evalAppl` enters counts once on entry: a variable's, a constant's, a
  bound name's or a definition's name included, each prefix of an infix junction, as SANY nests
  them, but not a `$Pair` or a literal.
- Nothing it counts is cached (memo tables, epoch caches, values computed once, the definition
  cache): a hit would skip what TLC counts. What TLC computes as it starts, a constant definition
  (`processConstantDefns`), counts nothing and is compiled as the engine always compiles it.
- No fused form stands in for an expression it counts: each closure is evaluated as TLC
  evaluates the node.
- An operator's argument and a LET's definition are TLC's `LazyValue`: evaluated at the first use,
  counted then, and kept for later uses in states that hold what the states of the first held
  (`isSubset`), where they count only the name. The machine keeps a cell for each, cleared as the
  application or the LET is entered. In a next state alone (a prime, UNCHANGED's second side) TLC
  keeps nothing and counts each use.
- The initial predicate and each of TLC's actions (`context.actions`) are walked as
  `getInitStates` and `getNextStates` walk them, not as the engine's walker does: a leaf of a
  next-state walk (a guard that holds, `x' = e`, `x' \in S`, UNCHANGED) counts once each time the
  walk after it added a successor; an initial state counts into the leaf that completed it and
  into its root; a LET of a walk binds nothing, so its definition is applied anew at each use; TLC's
  shortcut once every variable has a value evaluates what is left. No `pc` switch, guard
  ordering or pieces.
- Each invariant and constraint is checked whole on every state, none skipped because the step
  left what it reads unchanged. A constraint counts into its root where it is false and into the
  secondary count where it holds (`isInModel`).
- The search adds a step into its action's root, and a new state into the secondary count and
  each variable's `HyperLogLog(10)` estimate, of its fingerprint with `-fp`'s polynomial
  (`Worker.addElement`).
- One thread, no pipelining: the clause beside `is_shared`'s.

## Secondary counts

TLC counts an enumeration (`nextElement`, one for each element taken and one for the end it
reaches), and a conversion of a tuple or a record, into the cost model of the value, which the
node that built it gave it. The store hash-conses values, so the engine can't tell two objects
apart; the variant knows statically what a value carries (`Tag`): nothing, for a constant, an
integer interval or what TLC computed as it started; the wrapper of the set enumeration, set map
or set filter that built it in the evaluation that enumerates it, through arguments and
definitions; or it doesn't know, as for a value a state holds. It counts an enumeration of a set
it knows the builder of, a function construction's own count of its domain, and `S \cup T` of a
set T the expression built where S isn't empty; it declines an enumeration of a set it doesn't
know, and abandons, as it runs, a comparison, membership or sequence operator that may convert a
function between classes the store doesn't tell apart.

## Declining and abandoning

A model the variant doesn't follow is declined as it compiles; a run it can't count as TLC does,
which it finds as it runs, is abandoned: the search goes on unchanged and the report comes from
the replay. A run that stops (a violation, a deadlock) takes the replay too, which also counts
what TLC evaluates as it rebuilds the trace. Neither is a decline of the binary: the binary
declines only what the replay declines. `PROVE_IT_TEST_COVERAGE_COMPARE=1` runs both counters and
fails, printing the wrappers that differ, where the engine counted and the counts differ.

## The 5 minutes

TLC ends a report of a run past 5 minutes with 2777 (cli.md, "2777 rather than 2202"). The
replay's cut of 60 s rests on the replay being slower than TLC. The engine's search took at least
0.08 times as long as TLC on the perf suite (cli.md's table), and its counting variant longer, so
the engine's report prints for a run of at most 10 s, which TLC took at most about 125 s over, and
a longer run takes the replay and its cut as before. The ratio should be measured on Depot with the
counting variant before the cut is raised.

## Measured

The compare gate over the 189 corpus models whose report the replay prints, and the TLC sweep
(cli.md, "Sweep and performance"), at each piece:

| Piece | Engine counts | Differ from the replay | TLC sweep |
| --- | ---: | ---: | --- |
| The tree, the counting core, the walks, lazy values, the variables' estimates | 71 | 0 | 259 match, 456 decline, 0 differ |
| Enumerations of sets an expression builds | 86 | 0 | 259 match, 456 decline, 0 differ |

The sweep's counts are those before the engine counted: the binary declines no more and prints
no other report.

## What is left

- Memo hits that record the count delta of the miss and apply it on a hit, so the variant can
  cache: today it caches nothing it counts.
- Cross-step secondaries: the tag of a value a state holds, which the variant would carry beside
  the state, and `DiskStateQueue`'s spill past 8,192 states, whose values TLC reads back without
  one. Today an enumeration of a variable's set declines.
- Universal quantifiers in a walk, quantifiers of several bounds, recursion, lazy sets
  (`SUBSET`, `[S -> T]`, records' sets, products, `Seq`, UNION) and their memberships, functions
  TLC keeps lazy, and TLC's trace rebuilds after a violation.
