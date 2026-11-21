# No TypeScript engine fallback

**Superseded (PR 7, 2026-11-12).** The interpreter, the TypeScript checker and TLC 1.7.4's output
are deleted. The library's `check` and the CLI run the native check alone: where it declines a
model, `check` throws `TlaUnsupportedError` with `not native yet: <reason>`, and the CLI prints
`prove-it: not native yet: <reason>` and exits 1. `PROVE_IT_ENGINE=0` is gone. The rest of this
file records the plan as it stood before.

What `check` does where the native engine declines a model or can't be loaded, now that the
TypeScript engine is deleted. The plan was written for the owner on 2026-11-09 (branch
`fallback-plan`); the owner chose option C below the same day, and this records it as built.

## What a decline leaves

A decline prints `prove-it: not native yet: <reason>` on stderr and exits 1. Output is held for
the first two seconds of a run (`transaction.rs`, `HOLD`): a decline within them prints nothing
else, on stdout or stderr. After them the output streams as TLC prints it, so a slow decline
follows the TLC lines already printed: stdout may hold TLC's transcript up to the point where the
engine stopped, and stderr then ends with the decline's line. `main` does the same. The library and
the CLI of `dist/` print none of it ([cli.md](cli.md), "What a decline leaves printed"). A tool that
compares runs counts a decline with stdout within the hold, or with more than one stderr line, as
contaminated, not as a decline.

A decline also leaves the files the spec's operators write, and the `-dump` file it can keep, as
the run found them (`tla_values::written`); the files of `-userFile`, `-dumpTrace` and the trace
exploration spec, and a `-dump` file it can't read whole or of more than 64 MiB, it doesn't keep
(below). Each top-level check keeps a journal of its own. Its nested scopes
share it, and the threads it starts (the search's,
its workers, liveness helpers) take it with them, so two checks in one process never put back
each other's files. Before a Json operator or IOUtils's `Serialize` writes a file, the journal
keeps its bytes, or that it wasn't there. A symbolic link whose target isn't there is kept as its
target, which the write makes through the link and a decline removes, leaving the link. A scope
that declines puts back what it wrote, last first. One that ends without a decline leaves what it
kept to its parent, which may still decline. The outermost lets go of all of it, so a successful
check holds no file's bytes once it ends. A batch of specifications holds each spec's kept bytes
until the batch ends. A decline that fails to put a file back doesn't decline: it prints
`prove-it: a run that wasn't native (<reason>) couldn't put back <path> as it found it: <error>`,
so no other checker takes up the model over the files the run changed.

## A literal as an action

`Tool.getActions` fails as TLC builds its `Tool`, after the symmetry and before the assumptions,
on a literal it reaches through the body of the definition NEXT names, a LET's body, a label's
or a disjunct, which TLC reports as an exception with the literal's text. The engine reports a
numeral below 1000 written as its decimal digits, reached past disjuncts TLC takes whole without
evaluating them. A literal under an operator's application or an \E, which TLC swallows and
takes whole, another literal, whose text the IR doesn't hold as written, and a simulation keep
their declines.

## A variable or a constant as an action

On the same walk, a variable or a constant (`Next == x \/ x' = x`, `Next == x' = ~x \/ x`,
`Next == x`, `Next == c \/ x' = x` with `c = TRUE`), or one in the action of a SPECIFICATION's
`[][x \/ x' = x]_x`, makes `getActionsAppl` look the name up to its declaration or to the
constant's value, neither of which is an `OpDefNode`, and cast the declaration to one: a
`ClassCastException` TLC doesn't catch, so it stops at startup with exit 255 whatever the
variable's value. The native checker, like main, ran the search: with the variable FALSE it
reported "No error has been found" (exit 0), TRUE an incomplete successor (2109), and another
value a non-boolean next-state expression. The engine now declines it where TLC builds its `Tool`,
after the symmetry ("a variable or a constant TLC's splitting of the next-state relation reaches,
which it fails to cast to a definition as it starts"), and the front end with the same reason for
a SPECIFICATION's action under a LET (`Spec == LET A == x' = x IN Init /\ [][A \/ x]_x`), whose
scope the engine doesn't see. A literal TLC meets first (`Next == 3 \/ x`) keeps TLC's own failure.
Under an operator's application or an \E TLC catches the cast's failure, which this doesn't decline
(see "Known wrong outputs").

A declared constant the configuration substitutes a definition for (`CONSTANT C(_)` with
`C <- Op`, or `c <- D`), applied on the same walk, fails the same cast unless TLC splits the
definition: `getActionsAppl` finds `Op`'s OpDefNode through the constant and splits its body with
the arguments bound only where every argument is of constant level, inside a try; where one isn't
(`Next == C(x)`, `C(x')`, `C(1, x)`, `LET y == 1 IN C(x)`, `x' = x \/ C(~x)`), where an argument
fails to evaluate (`C(1 \div 0)`), or where the split of the body fails (`Op(v) == x \/ x' = v`
with `Next == C(TRUE)`, a literal or a formal parameter as a disjunct of the body, a nested
substituted constant that fails so), it casts the constant's own declaration, an OpDeclNode, to
OpDefNode, which it doesn't catch. The same holds of a SPECIFICATION's `[][C(x)]_x`. The native
checker, like main, ran the search: "No error has been found" (exit 0) where `Op` flips or keeps
the variable, an evaluation error (`C(x')`), an invariant's violation, or a trace naming `Op`
(`C(TRUE)` over `x \/ x' = v`). The front end finds this walk (`ActionSplitFailure::Constant`)
for the body of the definition NEXT names and for the action of each `[][A]_v`, and the engine
declines it with the reason above where TLC fails, after the symmetry. `Next == C(TRUE)`, `C(1)`,
`C(TRUE) \/ C(FALSE)`, `C(Nat)`, `\E i \in {1} : C(x)`, `D(x)` over `D(v) == C(v)` and
`[][Next]_x` over `Next == C(x)` split or are caught as TLC does and still answer.
An argument the front end's constant evaluator doesn't compute TLC may fail on as it splits
(`C(<<1>>[2])`, `C(Len(1))`, `C(Head(<<>>))`, `C([a |-> 1].b)`, `C({}[1])`, `C((1..2)[1])`,
`C(CHOOSE n \in Nat : n > 2)`, `C(CHOOSE n \in Int : TRUE)`, `C(CHOOSE s \in SUBSET Nat :
TRUE)`, `C(Assert(FALSE, "m"))`: TLC stops with the ClassCastException, exit 255, where main
reports "No error has been found"). Such an argument answers only where it is built of what TLC
evaluates without fail (`is_unfailing_argument`): literals, BOOLEAN, STRING, Nat and Int; tuples,
set enumerations, records, sets of records and of functions, products, SUBSET and Seq of such;
a filter or a function constructor over Nat or Int, which TLC keeps lazy (`SetPredValue`,
`FcnLambdaValue`), and its union with such a set; a function constructor over such sets whose
body is such; intervals and sums of numbers and tuples' lengths; `\o`, Head, Tail and Append of
tuples it writes; an element of a tuple it writes within it, a record's field it writes, and a
function's value at a number in its domain (`C(<<1>>[1])`, `C([n \in Nat |-> n][3])`, `C(LET
f[n \in Nat] == n IN f[2])`); and LETs and definitions of no parameters of such. Any other
declines, "a substituted constant applied as the next-state action to an argument the front end
can't tell TLC evaluates without fail as it splits the action"; main is wrong on all 29 probes
that decline so, and matches none.
An argument that draws doesn't fail: TLC draws once as it builds its `Tool` (between the constant
definitions it computes as it starts and the assumptions), binds the value to the parameter and
splits the body. Where the argument is a draw that can't fail (`RandomElement` of a set of numbers
it writes, as `{2-1, 2}` or `1..4`, or of SUBSET of one; `RandomSubset` of a size it writes, not
negative, of such a set, empty too, as `SubsetEnumerator` draws as many indices as it is asked
for and fails at none; their TLCEval, their sum with a number, their union with a set of numbers),
the body never names the parameter, and every other draw in the spec shows nothing of what it
draws either (one at such an argument, of several splits `C(RandomElement({1, 2})) \/
C(RandomElement(1..4))` or of two parameters, one of a set of one number, as `RandomElement({1})`,
or one in a constant definition TLC computes as it starts, before the split, whose body is such a
draw, as `K == RandomElement(1..30)` read by `ASSUME PrintT(K)`), the draw shows nowhere, and the
engine answers as main does (`action-split-constant-argument-drawn-unread`). Any other argument
that prints or draws declines, "a substituted constant applied as the next-state action to an
argument that prints or draws, which TLC evaluates once as it splits the action": where the body
reads the parameter, or another draw that shows follows the split, TLC's draw as it starts moves
on the generator the assumptions and the initial states draw from. Main matched those by chance:
with `Init == x = RandomElement(0..21) /\ PrintT(x)` (to `0..24`) beside
`C(RandomElement({1, ..., 7}))` main prints another x than TLC; with `Init == x =
RandomElement(0..3)` (to `0..10`) and `Op(a) == x' = IF x < 9 THEN x + 1 ELSE x`, where x shows
only in the number of states, main counts other states than TLC in all 8; with `ASSUME
PrintT(RandomElement(1..30))` (`1..31`, `1..40`, `1..17`) main prints another number. It matched
`Op(a) == x' = x` beside `Init == x = RandomElement(0..3)` (to `0..8`), and a draw of two
elements printed (`RandomElement({0, 1})`, `ASSUME PrintT(RandomElement({3, 4}))`), only as the
number of states doesn't depend on x there, or as the two draws agree at `-seed 4`.

## Action composition errors

The trace action splitter keeps the unresolved core symbols `\cdot`, `~>` and `-+->` whole as
TLC's `Tool.getActionsAppl` does (TLC then rejects a leads-to or a guarantee as a temporal formula
where it evaluates the action). SANY rejects redefining this builtin at module or LET scope. Where
TLC's actions can be split, replay prints its unsupported-composition exception and source stack
before evaluating either operand. False guards still skip it, and earlier conjunct failures and
effects keep their order. An explicit `tlc2.tool.impl.Tool.cdot` Java property declines before
startup, as does an explicit TLC 1.7.4 Jar profile.

The existing local-operator and INSTANCE replay limits also apply here: a parameterized LET
operator can prevent splitting and decline, and a composed action copied through an INSTANCE
with substitutions can print the application range in the first stack frame where TLC prints
the INSTANCE range. The latter remains a known wrong output.

## The chain

`check` (src/check.ts) tries, in order:

1. `getEngineIneligibility`. Some models never reach the engine: `PROVE_IT_ENGINE=0`, `-dump`,
   `-continue`, a periodic config and TLC 1.7.4. A spec without an initial predicate or a
   next-state relation doesn't either. The interpreter checks these, as TLC's semantics need and
   as the user asked.
2. The native engine (`checkNatively` in src/engine/native.ts). It returns:
   - `complete`: the search, which the interpreter replays only to check temporal properties and
     print a counterexample;
   - `stopped` or `invariant`: a violation, a deadlock or a run-time stop, with the search so far
     as a checkpoint the interpreter goes on from to print TLC's trace;
   - `declined`: the engine produced no state, and the interpreter checks the whole model;
   - `unavailable`: no engine loads, and `check` throws `EngineUnavailableError`.
3. The interpreter, which is the reference: it checks what the engine declines, goes on from a
   stop, and prints every trace.

The TypeScript engine was step 3 before, between the native engine and the interpreter. It is
gone, with `PROVE_IT_ENGINE_BACKEND`, `PROVE_IT_CODEGEN`, `PROVE_IT_STORE_TRACE` and
`PROVE_IT_MEMO`'s report. A decline now goes straight to the interpreter, which is correct but much
slower; the gaps workstream ([gaps.md](gaps.md)) takes the declines to zero.

## Where no engine loads (option C)

`getNativeAddon` loads, in order:

- the module `PROVE_IT_ENGINE_WASM` names, if set;
- where there is `process.dlopen` (Node, Bun): the addon `PROVE_IT_ENGINE_ADDON` names, the one an
  executable embeds, or the one in the platform package installed for this system; failing those,
  the WebAssembly engine the main package ships as `dist/prove-it-engine.wasm`, so an unlisted
  platform (riscv64, FreeBSD, win32 arm64 and so on), or an install without optional
  dependencies, still searches natively, on one thread. An addon named by `PROVE_IT_ENGINE_ADDON`
  or embedded is the only one tried;
- where there is none (a browser): the WebAssembly engine `loadWasmEngine` fetched and compiled
  before the check from beside the module, where a bundler copies it (DESIGN.md 7.4).

Where none loads, `check` throws `EngineUnavailableError` (src/errors.ts, exported). Its message
gives the loader's reason and says to install the package with its optional dependencies on a
supported platform, or to set `PROVE_IT_ENGINE=0` to check with the interpreter. The CLI prints it
and exits with 255, TLC's exit code for an internal error. Nothing falls back to a slower search
unasked.

Who reaches the error, now that the main package carries the WebAssembly engine: a host where it
fails to compile or instantiate, a build of `dist/` without it (`bun run build` alone, without
`platform-packages.ts build --target wasm32-unknown-unknown`), and a platform package from another
release (an ABI mismatch) where the addon is named or embedded.

### Decision: SANY's report needs the engine too

Settled on 2026-11-10, as the TypeScript SANY front end is retired (front.md): the CLI prints
SANY's report as tla-front writes it, through the addon or the WebAssembly engine. Once
`src/sany` is deleted, `PROVE_IT_ENGINE=0` means that the interpreter searches, not that no native
code runs: SANY's report still needs the addon or the WebAssembly engine. Where neither loads, the
CLI throws `EngineUnavailableError` for the report, worded for the front end, as `check` does for
the search. The TypeScript report is deleted: what it printed, tla-front prints or declines, and
its tests are tla-front's `tests/report-cases`, each recorded from TLC at d8fb231 or TLC 1.7.4.
TLC 1.7.4's warnings alone match (case 22), and its semantic errors decline (cases 19, 20, 34
and 35), which the TypeScript report printed: whether to port 1.7.4's generator differences or
retire them with 1.7.4 is open.

SANY's messages come from the port of its generator and levelCheck, which declines a message whose
shape no recording shows, and else from linking. Linking takes the standard modules as TLC ships
them, which a spec that replaces one another standard module reads, such as its own Naturals
under Sequences, may not keep: main's binary printed no errors for a Naturals without `..`, where SANY
reports 24 (tests/report-cases/38), which the generator now writes. Where the generator declines
such a spec, linking declines too ("SANY's messages of the standard modules with one of them
replaced").

Seven adversarial runs against TLC at d8fb231 (about 1,440 runs of 620 specs, 680 more specs,
2,149 runs of handwritten and corpus-mutated specs, 1,876 more inputs, 6,571 more, 951 of a
spec's paths and files, then 4,350 more, in TLC's default mode and with `-noGenerateSpecTE`) and review found the
report wrong or declining for 2,113; each is a case of tla-front's `tests/sany-cases`, recorded in
`sany-cases.json`, whose `case.json` gives the reason where the front end declines it.
Twenty-five more cases (`tlc-*`) are specs of the upstream conformance suite whose messages, such as "The
operator + requires 2 arguments." or "Symbol = is a built-in operator, and cannot be redefined.",
no recording had shown, recorded from the pinned jar with `-noGenerateSpecTE`. All print
what TLC prints but these, which decline:
- a module SANY's parser accepts and the front end's rejects (4 cases): proofs nested more than
  100 deep, where SANY's parser stops, and mutations whose parse the front end reads otherwise.
  The parser now reads a bound of the empty tuple, `\A <<>> \in S : P`, which SANY's parser
  takes and its generator binds as a tuple of one name, `>>`, the token after `<<`
  (`Generator.processQuantBoundArgs` takes every other token of the tuple from its second): so
  `\A <<>> \in {<<>>} : TRUE` fails as `\A <<y>> \in {<<>>} : TRUE` does (TLC's "Argument
  mismatch in operator application.%1"), the bound holds where no element is enumerated, and two
  of them in one scope are SANY's "Multiply-defined symbol '>>'". Probes of each binder (\A, \E,
  CHOOSE, a filter, a set map, a function and a recursive function's definition) over `{}`,
  `{<<>>}`, `{<<1>>}`, `{1}` and `{<<1, 2>>}`, nested and beside other bounds, in each context,
  match the jar or decline as they do with a name.
  The parser now reads a definition of the postfix operator `'` (`a' == a`, `a ' == 1`), which
  the generator rejects as a built-in, the prime as a primary expression (`'(e)` is `e'`; `'`
  alone or `'(a, b)` is its arity error), a selector after an operator's name (`^#(2)!1`,
  `\cup!1`, `'!x`), a prefix operator or the prime as a selector's name (`A!B!SUBSET(x)`,
  `Init!ENABLED`), and a CONSTANT declared as a prefix keyword (`CONSTANT SUBSET _`), which won
  9 of the 13. The implicit substitution `c <- c` of an INSTANCE for a declaration without
  parameters, where the instancer's `c` takes some, is reported as SANY's `SubstInNode` reports
  it, at the INSTANCE, even where WITH substitutes `c` (`OpDefNode.match`, `OpDeclNode.match`);
  linking declines two such reports in one INSTANCE, which SANY orders by its Hashtable
  (`implicit substitutions of an INSTANCE that SANY rejects in its Hashtable's order`), and one of
  an INSTANCE the parser gave no place to report at (`an INSTANCE without a place whose implicit
  substitution SANY rejects`), and the generator orders. The parser now reads
  SANY's `\land(A, B)` and `\lor(A, B)`, LOCAL in a LET, and a subscript of `]_` or `>>_` that is
  a set, a function, a record or an EXCEPT, or a name whose arguments SANY leaves out of the tree
  (`[A]_V(x)` is `[A]_V`), which won 23 of the 36;
- a definition's prefix operator parameter written `~ _`, `\neg _`, `¬ _`, `□ _` or `◇ _`, which
  the parser rejects so the report declines: SANY names it by its image as written (`getUS` in
  `processOperator`, which resolves the synonyms of infix parameters only), so `\neg _` is
  reported as `\neg` and `~ _`, `¬ _`, `□ _`, `◇ _` declare names that aren't built in. Main
  reported "Symbol \lnot is a built-in operator" (or `[]`, `<>`) for these, which TLC
  doesn't;
- a module of the CommunityModules that no file beside the spec holds, or a module of TLC's that
  extends one, such as `_DotTrace` or `_CBORTrace` (155 cases): TLC finds it where
  CommunityModules.jar is beside tla2tools.jar, and else reports it missing, which the TypeScript
  report printed;
- SANY's generator throwing on the root module after a module of the user's (2 cases; main's
  binary declined);
- a HIDE of an expression SANY's generator leaves null, such as `HIDE 1 + 1` without Naturals,
  for which SANY throws a NullPointerException (9 cases);
- a record field named like a definition whose value applies a recursive operator, on which
  SANY's linter overflows its stack (4 cases);
- `@` as a DEF clause entry, which SANY reports as an unknown operator (2 cases);
- a module nested at the top of a module that its extender extends, which
  ParseUnit.handleExtensions lets the extender's EXTENDS and INSTANCE name, and the front end
  looks for in a file, where the loader that binds names to inner modules of extended files
  doesn't bind them unambiguously (12 cases; it prints the other 9 of the 21 as TLC does);
- LETs nested 100 deep in their definitions, where SANY's generator throws (1 case);
- brackets nested so deep that SANY's parser may overflow Java's default stack: past 1,100,
  counting a square bracket twice, where Java overflows past about 1,500 parentheses, braces or
  angle brackets and 900 function constructors. Other forms nested as deep, such as IF or `\A`,
  are not counted, and may print where TLC overflows (1 case).

Linking declines a parameterized INSTANCE of a standard module, whose operators it gave no
parameters (`I(p) == INSTANCE Integers` with `I(1)!Int`): main's binary printed that `I!Int`
requires -1 arguments. Where the binary declines, the CLI falls back to the TypeScript engine,
which still prints that error after SANY's report, as it prints other errors its linking raises,
such as for `EXTENDS _JsonTrace`, as SANY's. How TLC finds, reads and names a spec's files, which
the last run probed, is TLC's resolver's, as main has it; what that run found there is for the
resolver, not the report.

TLC prints a character of a message outside ASCII as `?` under a locale that isn't UTF-8, where
Prove It prints the character; the runs above compare under `C.UTF-8`. The CLI's own command line,
which names several specs, a spec by its configuration file or a glob, is not TLC's.
A batch without `-config` keeps that launcher behavior. With `-config`, one specification is
required; a second input reports TLC's first command-line error, before later invalid options
and using only `-tool` flags already read. A nonempty option-only invocation also reports TLC's
missing-module error, including when an option consumed the apparent module as its value.
An invocation with no arguments keeps the launcher's own usage text.

A message of the generator whose shape no recording shows is printed where linking gives the same
messages, and where linking can't give them, as the TypeScript report, a port of the same
generator, printed them; where linking gives others, the report declines ("SANY's messages,
which linking gives apart from SANY's generator").

Linking and lowering read a module as SANY's report does: a carriage return that no line feed
follows ends a line (and a `\*` comment), where the model's lexer read on and raised an error SANY
doesn't ("an error tla-front raises that TLC reports without a code"); and the module order takes
`EXTENDS` or `INSTANCE` followed by `|->` or `:` for a record's first field, as SANY's parser does
(`[EXTENDS |-> 3]`), not for a module named `|->`.

An invariant whose declared constant the configuration replaces by an operator holding `[]`, `<>`,
WF or SF under ENABLED (`CONSTANT C <- G`, `Inv == ENABLED C(1)`) passes SANY's level check, which
sees the declaration: TLC reads the invariant's level as SANY gave it and fails where it evaluates
the ENABLED ("In computing ENABLED, TLC encountered a temporal formula", or "temporal
quantifier" for `\EE` and `\AA`). The front end's level
check of the substituted invariant, which rejected it with no code TLC prints, now reads SANY's
levels there. An invariant whose substitute raises SANY's level to an action or a temporal formula
is evaluated as TLC's `Tool.isValid` evaluates it, of the state alone: a prime, an UNCHANGED or an
action's subscript it reaches outside ENABLED fails as on an initial state ("In evaluation, the
identifier x is either undefined or not an operator"), and so does a CONSTRAINT's
(`Tool.isInModel`), where the search would otherwise have read the successor it holds.
A PROPERTY's state-level warning (2255) likewise reads SANY's level (`OpDefNode.getLevel` in
`processConfig`), not the substituted one: `P == x # 0 \/ Op(TRUE)` with `Op <- T` and
`T(a) == x' = 1` is warned of as state-level before `getLevelBound` finds it an action (2272), and
a substitute that lowers SANY's action or temporal level to a state's is not warned of. A property
SANY's level check would reject before its substitute declines ("a property SANY's level check
rejects before its substitute").

A theorem's ASSUME/PROVE of expressions is selected as SANY selects an operand (`T!1` its first
assumption, `T!2` after one assumption its goal), as a `$Nop` application of the clause at the
selector. A clause that declares (NEW) or nests an ASSUME/PROVE, and `T!<<` or `T!>>`, still
decline in the engine ("unsupported: expression Subexpression").

The replay words what `getInitStates`, `getNextStates` and `Tool.enabled` reject themselves, as
the action walk meets it: a premise of `=>` that isn't a boolean ("In computing initial states of
a predicate of form P => Q, P was an integer\n.", "In computing next states ...", "While computing
ENABLED ..."), a value that is no set (a scalar, a tuple, a record or another function) on the
right of `\in` an assignment reads ("the right side of \IN is not enumerable"), and a quantifier
or CHOOSE without a bound that ENABLED walks ("In computing ENABLED, TLC encountered unbounded
quantifier."). An unbounded CHOOSE or quantifier ENABLED evaluates as a value, which TLC words as
`Tool#eval` does, still declines.

A temporal formula's quantifier over a set TLC knows only by name (`\A p \in Nat : WF_v(A(p))`,
`\A n \in Int : <>P` as a property) fails as `Liveness.astToLive` and `processConfigProps` meet it
in `Tool.contexts`, with TLC's "non-enumerable quantifier bound" in the 2213 report, after the
bounds before it; and the constant evaluator computes a function application's function first, as
`Tool`'s OPCODE_fa does, so a state-dependent bound (`\A p \in {q \in S : pc[q] = 0} :
WF_pc(...)`) fails on the variable as TLC does. `processConfigProps` computes the sets of a
property's `\A` whatever their level, so an EvalException in a set that reads the state, before
the state is read (`\A a \in {(1 \div 0)[x]} : <>P`), escapes TLC's startup (1000 with the
message) as it does for a constant set; a failure on the variable is left to the liveness
checker's 2213. A substitute the configuration gives a constant that holds `[]`,
`<>`, WF or SF (`CONSTANT C <- T`, `T == <>P`) fails as `Tool#evalAppl` does where
`processConstantDefns` computes it (2281 with 2261). A tuple binder (`\A <<p, q>> \in ...`), a
`~>` substitute and an arithmetic failure in a constant subformula (`(1 + "a" = 2) => <>P`) still decline ("..., which
the constant evaluator doesn't compute").

A module's dependencies are the modules ParseUnit.getInstances finds walking every unit of it in
preorder, in the module and in the modules nested in it: definitions (a function's bounds before
its body), INSTANCEs with the expressions their WITH substitutes, ASSUMEs, THEOREMs with the sets
of their `NEW` symbols and their proofs, and module-level USEs and HIDEs; a LET's definitions and
INSTANCEs in the order they are written. The report took a LET INSTANCE in a `NEW` symbol's set,
in a substitution, or in a USE or HIDE (and in a THEOREM or ASSUME of a nested module) for no
dependency, and reported a later missing module or none, as main did; and a proof's INSTANCE
declined (72 sany-cases), which all now print what TLC prints. The front end still declines a
proof's INSTANCE of a module that its dependencies miss ("SANY's report of a proof's INSTANCE of a
module SANY loads"), which no known spec reaches.

SANY's parser rejects a function definition with a LET in a bound (`f[n \in LET x == 1 IN {}] ==
1`), at any depth: TLAplusParser.belchDEF puts the DEFBREAK that begins a definition before the
first `==` after the definition before, which is the LET's, so the function's name begins none.
The front end's parser accepts it, where main printed no error; the report now asks the port of
SANY's parser (`get_sany_parse_error`) for its report there, and declines if that accepts the
module ("a function definition whose bound holds a LET SANY's parser accepts").

### Decision: the CLI finds a spec's files with the engine

Settled on 2026-11-11, as the CLI's TypeScript copy of TLC's resolver is deleted: the CLI finds the
spec, its config, its modules and its Java overrides as the binary does, through `prove-it-host`'s
`resolveFiles` and `checkSources`, which name the paths they stat, read and resolve, the working
and temporary directories and the platform, for JavaScript to answer. Paths follow the host's rules
(`prove-it-check/src/host_path.rs`, Node's `path` for the platform, as the TypeScript resolver used
it): the binary and the addon take them from the target they were built for, and the WebAssembly
engine from the platform JavaScript names, so a Windows host without the addon reads `;` lists,
drives and UNC paths. So `PROVE_IT_ENGINE=0` means, here too, that
the interpreter searches, not that no native code runs. An install without the platform package
checks with the WebAssembly engine beside `dist/cli.js` (`tests/unit/native.test.ts` runs a copy of
`dist/` that no package resolves from). The CLI throws `EngineUnavailableError` only where an engine
`PROVE_IT_ENGINE_ADDON` or `PROVE_IT_ENGINE_WASM` names, or an executable embeds, fails to load, or
where neither the addon nor the WebAssembly engine loads. Its message then names no setting, since
none checks without the engine. The library's `check` of a source string reads no file and is
unchanged.

The engine reads nothing itself: an export that reads what JavaScript holds, such as a spec's
modules, names what it needs and is called again with it (`prove-it-host`'s `sources`), so the
WebAssembly engine needs no file system and calls nothing in JavaScript.

### Decision: the WebAssembly engine ships in the main package

Settled on 2026-11-10 (#166): the engine as WebAssembly ships inside `@atemp/prove-it` as
`dist/prove-it-engine.wasm`, not as a separate `@atemp/prove-it-wasm32` package. A browser bundler
copies only an asset a literal `new URL("./…", import.meta.url)` names beside the module that names
it, as it copies the workers, and a browser can't resolve a bare package specifier without an
import map, so a separate package was never found once bundled. It costs every install about
1.3 MB, and in return every install has an engine: the browser's, and Node's or Bun's where no
platform addon loads.

## Where the interpreter remains a fallback

- **A decline.** The engine declined before producing any state.
- **A stop.** A violation or a deadlock hands over the search so far, and the interpreter prints
  TLC's trace from it. A run-time stop the engine doesn't model does the same.
- **A WebAssembly trap.** The engine's frames are on the host's call stack there, which is
  shallower than the addon's search thread, so a deep recursion can trap. The loader replaces the
  instance and returns a stop that hands nothing over (src/engine/wasm.ts). The CLI's interpreter
  then searches from the start; the library's check throws `WebAssemblyStackError` instead, as it
  does where the engine stops at its recursion bound.

### Interpreter limits

Where the native check declines, the library's `check()` passes the TypeScript check's prints of
a violation's trace to `onPrint` as TLC prints them, but for three shapes, where the TypeScript
check places them otherwise than TLC or prints other values in them: an ALIAS that prints, a
temporal property that prints, and TLCExt's `Trace`. There `onPrint` gets what the TypeScript
check printed as it searched, as where the native check doesn't run (`onProgress`, `onPause`, a
`dot` dump, TLC 1.7.4). `tests/unit/trace-prints.test.ts` pins them; they go with the interpreter.

Each of these reports itself under `PROVE_IT_ENGINE=debug` (`native: declined: …`,
`handed over after …`).

## What was deleted

The TypeScript engine's search and compiler, about 7,400 lines: `src/engine/compile.ts`,
`action.ts`, `codegen.ts`, `memo.ts`, `context.ts`, `search.ts`, `live.ts`, `symmetry.ts` and
`state-log.ts`. The types the native path still uses (`EngineCheckpoint`, `EngineResult`,
`EngineGraph`, `LiveOracle`) moved to `native.ts`, and `IrSpec` to `ir.ts`.

With it went its tests (the memo tables, the store trace, `ts-only-tests.json`), the scripts that
read its internals (`native-expressions.ts`, `native-replay.ts`, `store-replay.ts`), the `ts`
backend of the conformance scripts and the Parity pairs that named it (`ts/rust`, `tlc/ts`,
`ts/interpreter`, `ts/stopped`), and `coverage-allowlist.json`, which gated the native engine's
coverage against it. The native search tests that compared state logs with it now compare the
native state log with the states the interpreter writes to TLC's `-dump`, in TLC's order.

What stays: `ir.ts` (the TypeScript front end's lowering, until `tla-front` replaces it);
`store.ts`, `convert.ts` and `fingerprint.ts`, the bridge that decodes the native states for the
interpreter and the store tests' oracle; `native.ts`, `wasm.ts` and `settings.ts`; and the
interpreter, with `PROVE_IT_ENGINE=0`.

## Tests need the engine

Every check needs an engine, so `bun run test` builds the addon for this system
(`platform-packages.ts build`) before it runs, and `tests/setup.ts`, which `bunfig.toml` preloads,
points `PROVE_IT_ENGINE_ADDON` at it unless it or `PROVE_IT_ENGINE_WASM` is set. Running the tests
needs the pinned Rust toolchain; Verification's Test task and Release's test step bootstrap it.

## Retiring the interpreter

The owner asked on 2026-11-10 for the interpreter to go too, after the TypeScript SANY front end
and alongside the prover's port to Rust. This is the plan. Nothing is deleted until its stages
are green.

### Measured on main

- **The library declines 15 models** of the 733 Conformance models TLC checks in 20 s or less, each
  under a second:
  - TLCSet (8): ConstantContextTLCCache, DieHardTLA, EWD998Chan, TLCGetNonDeterminism, TLCSetInit,
    Test2, ChainedCdots and NQSpec/MC;
  - TLCGet (2): MCDieHardest and test220;
  - printing a value whose text depends on how TLC built it (2): FastMutex2 and FastMutex3;
  - JsonSerialize (1): EWD840_json;
  - AssertError (1): Github696;
  - a definition TLC computes at startup that fails there (1): test23.
- **The binary prints what TLC prints for all 15.** The native-only differential runs 1466 runs
  (733 models in two modes). 1460 print what TLC prints and the other 6 are known differences. None
  says `not native yet`.
- **The engine already covers the corpus.** The interpreter survives because the library doesn't run
  the binary's pipeline. The library lowers the engine IR from the interpreter's `Environment`
  (`src/engine/ir.ts` imports `evaluate`, `liveness` and `values`), and prints through the
  interpreter. The binary goes from `tla-front` to the IR, the engine, and `tla-trace` and
  `tla-live`, and prints TLC's output itself.

### What the interpreter still does

Besides the 15 declines, it does the following in the library:

- **Stops.** 131 of those models stop: a deadlock (54), an invariant (33), an initial state (7) or
  a run-time error (about 37). The interpreter re-derives the expanding state and prints TLC's trace
  (`resumeFromEngine`, `tlc/replay.ts`). The binary prints these natively (`tla-trace`).
- **Temporal properties.** The interpreter prints the lasso or accepting counterexample from the
  native graph. Under SYMMETRY or a VIEW, or where `tla-live` declines, it checks the properties
  again. The binary prints lassos and accepting counterexamples, including a lasso under SYMMETRY or
  a VIEW, whose states it re-creates from the previous real state's successors as TLC's
  `LiveWorker.printTrace` does with `getState(fp, previous)`. It declines an accepting node under
  SYMMETRY or a VIEW, an unexpanded graph and uncounted branches. None of these occurs in the
  corpus or the library's tests ([below](#liveness)).
- **Models without a search.** 44 models have only constants and ASSUMEs. The interpreter also
  checks every model's assumptions, and computes the initial states of a spec without a next-state
  relation. The binary does all three.
- **What `getEngineIneligibility` keeps from the engine:** `PROVE_IT_ENGINE=0`, `-dump`, `-continue`,
  a periodic config and TLC 1.7.4. The binary says `not native yet` to `-dump`, `-continue` and
  TLC 1.7.4. The engine doesn't support a periodic config either.
- **A WebAssembly stack overflow.** The library's check throws `WebAssemblyStackError`; the CLI's
  interpreter searches from the start.
- **`PROVE_IT_LIVE_CHECK=1`.** It cross-checks the native liveness verdict.

The interpreter implements none of `-simulate`, `-generate`, `-debug` or `-loadTrace`; the binary
runs `-simulate` and `-generate` and declines the cases cli.md's "-simulate" lists, and the rest. The binary writes
`-dumpTrace tlc` and `-dumpTrace json`, and declines the other formats and the cases cli.md's
"-dumpTrace" lists; the interpreter writes none. A root module that extends `_JsonTrace` or
`_TLCTrace` and whose configuration names its postcondition and assigns its two constants
(`POSTCONDITION _JsonTrace`, `CONSTANT _JsonTraceFile = "trace.json"` and
`_JsonTraceInputFile`) checks the postcondition -dumpTrace adds, and the binary writes the file
as it does for -dumpTrace; linking gives the root module the module's constants, and SANY's
string order reads the module where the root module's EXTENDS names it, so TLC's order of the
module's strings is kept (a JSON dump of a state holding them is byte for byte the jar's).
Beside -dumpTrace, -postCondition, -inv, -dfid, -simulate or the trace exploration spec, or
where the configuration doesn't name the postcondition and the constants so, it declines ("a spec
that extends a trace module ..."); so does an ALIAS, as for -dumpTrace. It prints `-coverage`'s report and declines the
cases cli.md's "-coverage" lists: its "Not native" list, the cut, `-continue` carried past a
violation, and estimates without `-fp` that differ by polynomial.
`src/pcal` only validates for SANY, and `src/prover`, the wrapper of the Rust prover driver,
imports only `worker.ts`'s thread helpers (`isWorkerSupported`, `spawnWorker`,
`getParentPort`). Those move to the prover. `tlc/version.ts`, `tlc/jar-data.ts` and
`tlc/messages.ts` are shared with the front end and the CLI, so they move too.

### Every `check` of the library's tests, through the binary

`bun scripts/run.ts check-log` measures this; it is the retirement's progress meter. It runs
`bun test` with `PROVE_IT_CHECK_LOG`, under which each `check` given its configuration as text writes
its source, configuration, options and calling test, and each module, override class and file it
reads. Then it runs each distinct check through the binary with TLC's command line for its options.
Each check runs on one thread and with every level shared between four, and once more on one thread
without `-noGenerateSpecTE`, as TLC runs by default. A run a signal ends counts as not native.
`--json` writes each check with its answers.

What changes what a check does, and whether the meter keeps it. A setting it keeps is logged, part
of the key that makes two checks one, and given to the binary:

- Kept: the source and configuration, which hold `CHECK_DEADLOCK` and the constraints; the modules,
  override classes and files the check reads (a file the check reads by an absolute path, or outside
  its directory, the binary reads where the test left it); the seed; `-lncheck`; `-workers`; `-tool`;
  `-nowarning`; `-dump` with its format; `-continue`; TLC 1.7.4; the Java system properties `TLCGet`
  reads; and `PROVE_IT_TEST_LIVE_CHECK_AT`, which has the search check the temporal properties at a
  state.
- Fixed by the meter: `-fp 0`, the only fingerprint the library takes; and `PROVE_IT_WORKERS` and
  `PROVE_IT_SHARED_LEVEL`, since the meter runs every check on one thread and on four with every
  level shared.
- Not kept, on purpose:
  - `PROVE_IT_ENGINE`, which turns the engine off or reports what it did, and `PROVE_IT_STOP_AT`,
    which stops the engine's search to make the library fall back. The meter asks whether the binary
    checks the model, whatever the library did with it.
  - The self-checks `PROVE_IT_LIVE_CHECK`, `PROVE_IT_FINGERPRINT`, `PROVE_IT_FP_VERIFY`,
    `PROVE_IT_EPOCH_CHECK` and `PROVE_IT_MEMO=off`. Each computes an answer another way and fails
    where the two disagree, without changing it, and the binary reads none of them.
  - `PROVE_IT_STATE_LOG`, which only writes the states found, and `PROVE_IT_TEST_IR`, which only the
    binary's own tests set.
  - Whether the caller printed SANY's report, which the binary always prints, and whether TLC records
    a trace, which the default-mode run covers.
  - A configuration given as an object, as by the command line with `-deadlock`. The binary's tests
    and the differentials run that command line.

Measured at main 6871cd2, with the log as this section gives it:

- 1,885 checks. 1,218 print TLC's output natively. Their exit codes are 0 (559), 150 (168), 12
  (103), 10 (94), 75 (93), 13 (81), 151 (52), 255 (29), 11 (13), 14 (11), 76 (9) and 77 (6).
- 667 are `not native yet`, for 206 reasons, grouped below and listed in full after.
- One thread and four gave the same answer for every check.
- In TLC's default mode, which generates the trace exploration spec (the same checks without
  `-noGenerateSpecTE`), 245 are native. 1,412 decline as "SANY's report of the trace exploration
  spec TLC parses with the spec".
- None used `-continue`.

| Kind | Runs | Reasons | Test files (runs) |
|---|---:|---:|---|
| The command line (`-dump`, TLC 1.7.4) | 168 | 2 | `native-sets` 58, `check` 50, `native-search` 23, `native-builtins` 15, `state-graph` 11, `tlc-replay` 5 … |
| Rebuilding a run-time failure | 161 | 60 | `check` 58, `engine` 49, `native-builtins` 29, `native-search` 8, `operator-constants` 4, `tlc-replay` 4 … |
| Rebuilding a failing assumption | 94 | 38 | `check` 70, `bags` 18, `json` 1, `exit-codes` 1, `tlc-ext-operators` 1, `tlc-revision` 1 … |
| The engine stops the search | 86 | 34 | `check` 31, `native-builtins` 17, `engine` 8, `exit-codes` 6, `native-search` 5, `tlc-replay` 4 … |
| The engine declines the model | 50 | 23 | `check` 12, `native-search` 11, `native-sets` 7, `tlc-ext-operators` 6, `engine-print` 4, `operator-constants` 3 … |
| Front end, configuration and printing | 44 | 22 | `check` 13, `overrides` 10, `engine-print` 5, `alias` 4, `printing` 3, `possible` 3 … |
| Temporal properties | 40 | 20 | `check` 12, `native-search` 8, `tlc-replay` 4, `tlc-live-level` 4, `temporal` 3, `engine` 3 … |
| Constant evaluation | 24 | 7 | `check` 10, `engine` 5, `exit-codes` 2, `bags` 2, `engine-print` 1, `instances` 1 … |

#### Liveness

Measured again on main f941e35 with a check that fails on a deadlocked state, what a model with
temporal properties prints at a stop, and TLC's errors for a tautology and a non-boolean constant
part, with `check-log` counting TLC 1.7.4's checks apart (63, retired with the interpreter): 287 of
the other checks have temporal properties, 245 are native and 42 are not. 12 of those 42 are the
liveness part of this plan, down from 22:
- a failure in a model with temporal properties: an atom of the temporal properties that may fail
  to evaluate, and SUBSET of a non-set evaluated again after Next fails (1 each);
- a division by zero in Next where a late node of that state runs Next again, which TLC fails on a
  second time, evaluating the checks again (1);
- printing where the native checker doesn't check the temporal properties (5): prints it doesn't
  place in TLC's order (2), a node that accepts every behavior, a predicate the engine leaves to the
  interpreter, and steps from states it didn't store (1 each);
- an atom the engine doesn't answer, a late node at another diameter, a step back into the cycle of
  a spec that prints, and several states under VIEW or SYMMETRY (1 each).

Of the other 30: constant evaluation (9), a constraint, a VIEW or an action property that fails on
a successor (8), a power set too large to build (3), `-dump` (3), PrintT where the engine can't
place it (2), and five more of the evaluator's and the front end's gaps (1 each).

A deadlock in a model with temporal properties prints TLC's output where a check fails as TLC adds
the deadlocked state to the behavior graphs: the deadlock, the trace, then that check's call stack
([liveness.md](liveness.md)). It declines a check that reads a definition an INSTANCE copies, whose
call stack in TLC holds the INSTANCE as a frame. A spec that prints, stopped by a deadlock, a violated invariant or
action property, or a failure of Next or an invariant, prints what TLC prints at the stop, in TLC's
order, the prints of adding the stopped state after the trace included (liveness.md, "Print at a
stop"). It declines a late node of a state whose next states fail, one whose full Next takes
other steps than the search took, and an invariant that prints which the configuration lists twice,
which TLC checks twice.

The corpus has no temporal decline: `differential --native-only` matches 1,460 of 1,466 runs, and
the 6 known differences aren't about liveness.

A lasso that ends in the first state of its cycle (the `temporal` test's three runs) is a printing
gap. TLC prints every state, then stutters at the cycle's first state, and so does the binary now.
A grid of 160 small specs (`prove-it-cli/tests/lasso-grid`) prints what TLC prints on all 640 runs:
one thread and four, checking the properties periodically and at the end.

A property TLC finds a tautology, and a constant part of a temporal formula that isn't a boolean,
are native. TLC stops at a property's \A over the empty set as it unrolls the properties
(`SpecProcessor.processConfigProps`), and at a formula whose negation has no solution
(`ModelChecker.modelCheckImpl`), with `EC.TLC_LIVE_FORMULA_TAUTOLOGY`. It stops at a constant part
of a temporal formula whose value isn't a boolean (`Liveness.astToLive`) with
`EC.TLC_EXPECTED_VALUE`, which names the part by `SemanticNode.toString`: a numeral's image, such
as `\b101`, or else the part's location. Where the part is an expression an INSTANCE puts in for
a declaration of the module it instantiates, TLC's `SubstInNode` keeps the declaration's node and
binds it to the expression's value (`Liveness.astToLive`), so TLC names the declaration where the
instantiated module writes it, which the front end doesn't keep: that declines wherever the part
is, or is within, a substitute or what the front end makes of one (a LET or IF it folds, an
operator it calls, a substitute a later INSTANCE or a renaming copies). TLC takes a property's
label whole, and unrolls a property's \A with the substitutions of the INSTANCEs it went through
left unbound, taking the \A whole where reading one fails (`SpecProcessor.processConfigProps`).
The front end can unroll a \A with substitutions bound that TLC leaves unbound. It declines a
tautology or a nonboolean constant part when that richer context cannot justify TLC's result
(see "Declines to win back"). A grid of 113 small specs
(`prove-it-cli/tests/live-startup-grid`) prints what TLC prints on 608 of its 904 runs; the others
decline, for the constant evaluator's gaps, a substituted declaration, an unrolled \A, a constant
definition TLC may print as it starts before the error, or a tautology
after a state-level property, which TLC warns of first. Four name an
INSTANCE's definition before the INSTANCE, which SANY doesn't know there.

Nothing reaches these liveness declines, so they stay declines until a test or a model does:
- an accepting node under SYMMETRY or a VIEW;
- an unexpanded graph;
- uncounted branches;
- every decline of atoms that read or set TLC's registers.

One corpus model stops at an atom the engine doesn't answer: MisraReachability's MCParReach,
whose `PROPERTY Refines` is `R!Spec`, with `R == INSTANCE Reachable WITH vroot <- vrootBar, pc <-
pcBar`. The engine doesn't compile the action atom of `R!Spec`, whose `\E v \in vroot` enumerates
the substitute `vrootBar == vroot \cup UNION {toVroot[i] : i \in Procs}` read in the INSTANCE's
scope: a set TLC keeps lazy, of which the compiled substitute keeps no reference (`enumerating a
set TLC keeps lazy (vrootBar@ParReach: \cup at line 0)`). An atom the engine doesn't answer is one
TLC may fail at as it adds the initial state, so the search stops there, and replaying the atom
finds no failure: the binary and the library decline it ("the engine stopped: an atom of the
temporal properties that may fail to evaluate: evaluating the failure again: it didn't fail"),
where TLC checks it (747 states generated, 393 distinct). Written in the root module as
`R!Init /\ [][R!Next]_R!vars /\ WF_R!vars(R!Next)`, the property is native: TLC and the binary
both fail there ("In evaluation, the identifier vroot is either undefined or not an operator.").
Winning it back takes compiling a substitute's set with its lazy reference where an atom reads it
in an INSTANCE's scope.

The property reader reports TLC2253 when constant-domain universal quantification has no
contexts, before inspecting its body or later configuration requirements. Every domain
is evaluated before emptiness is tested, including malformed later domains. Earlier
invariant, subscript and state-property warnings keep their order. Empty tuple domains
need no binding; nonempty tuple binding retains its existing limitation. Complete
constant-TRUE properties are ignored, while empty universal subformulas reached during
temporal decomposition are rejected. Live bound effects and startup-definition print
replay retain their previous declines; dead effects in an empty body are not evaluated.

An empty expansion reports error 2253 only when every domain and every enclosing unroll has a
path-local proof of the context TLC uses. Configured source definitions, rewritten operators,
TABLE or opaque methods, state or printing effects, and external implementations cannot supply
that proof. Pure alias traversal has a termination guard. An empty filter or map can skip its
body only after its domains are certified empty. Otherwise the checker declines with
`a property's \A emptiness is not certified for TLC's context`; nonempty expansions keep their
previous behavior. A Java override index also invalidates this promotion until its effective
property and domain targets are known. This restores the 32 `Live095`, `Live098`, `Live105` and
`Live114` regression cells to their earlier declines while retaining the 24 upstream gains.
The `empty-universal-context-*` and `empty-universal-index-*` fixtures record neighboring cases.
Twenty-two such Java/index controls decline, as they do on main. Recovering those matches requires target and initialization provenance, rather
than treating an unreported or unread index as absent.
The proof also requires a closed Java operator context, including every reachable module class.
Opaque Java profiles or a present or uncertain override index prevent promotion, even through
labeled properties. Virtual sources can supply an explicit absent-class-space witness. Two
literal-empty controls under an opaque extra classpath decline, as they do on main. Their recovery needs an execution-context
proof, not an assumption that a literal's effective implementation cannot be overridden.

A formal next-state action reached directly through TLC's splitting prefix reports the
`FormalParamNode` to `OpDefNode` cast failure. Global and LET aliases, existential quantification,
subexpression selection and nonempty INSTANCE substitutions preserve their separate boundaries.
The new diagnostic declines when preceding startup effects or scoped/external evaluation cannot
be certified (`what TLC evaluates before a formal next-state action's cast fails`: a definition TLC
computes as it starts that may print or has an effect, an unknown startup or subscript check, a
TLCOverrides index or a module's external Java class), which covers three neighbouring shapes the checker once answered wrongly. TLC keeps a
LabelNode as a whole temporal conjunct rather than decomposing its body.

#### Action constraints that fail to evaluate

An ACTION_CONSTRAINT that fails to evaluate on a step is native: TLC throws out of
`Worker.addElement` before it counts the successor as found and reports the error as one of the
next states (`ModelChecker.doNextFailed`), with the trace to that successor, then the call stack of
its replay of the expansion with its `CallStackTool` (`ModelChecker.doNext`), as in
`prove-it-cli/tests/action-constraint-failures` (from the grid of 796 runs: 744 match, 52
decline, none differ). What still declines:
- an action constraint that is a literal and no boolean (`AC == "yes"`): TLC fails casting the
  definition it holds for it, with a ClassCastException whose message names the JVM's classes
  (`a constraint that is a literal, which TLC fails to cast`), as for a CONSTRAINT;
- one that fails under `-continue`, or with an ALIAS, `-dumpTrace`, a property TLC checks of each
  step (`[][A]_v`), or online liveness checking;
- one that fails past the expansion of the one initial state with several workers, whose others
  race the stop (under "A constraint that fails on a successor");
- one after which an atom of the temporal properties fails as TLC adds the state it was
  expanding to the behavior graphs: TLC then prints the atom's call stack with the trace to the
  successor, which isn't followed;
- one whose replay doesn't follow TLC: a successor before it TLC fails to fingerprint, one
  outside the model that violates an invariant, a next-state relation the evaluator doesn't split
  into TLC's actions, or a step that no longer fails;
- one the configuration binds (`= TRUE` outside a module scope, or `<-`), whose definition the
  search evaluates where TLC holds the value and drops the constraint bound to TRUE (`a failing action constraint the
  configuration binds`);
- a CONSTRAINT or a VIEW that fails to evaluate on a successor, as before (`a constraint, a VIEW
  or an action property that fails on a successor`).

A VIEW that fails to evaluate on an initial state is answered as TLC reports it: the error after
the constraints held, with the initial predicate's call stack, since TLC evaluates the VIEW outside
its `CallStackTool`. It still declines under SYMMETRY (`a VIEW that fails on an initial state`),
where TLC evaluates the VIEW of the state's least permutation, and in a method of a value with a
source (`a VIEW that fails in a method of a value with a source`).

The evaluator of failures declines one that reads a register (`a failure that reads a
register`): the search sets the registers in the order it explores the states, which the path
TLC's report replays doesn't follow. A model with no TLCSet, no TLCGetAndSet and no Java class of
the user's sets none, so TLC reads every register unset wherever it reads one, and the engine's
stop at `TLCGet of a register TLC hasn't set` goes to that evaluator, which words
`TLCGetSet.TLCGetEval`'s "TLCGet(42) was undefined.". TLCGet of a string that names none of
the keys `TLCGetStringValue` knows (the run's counts, "stats", "config", "revision", "spec",
"level", "action", "all", "all:named"), no named register ("s:") and no system property ("-D")
fails there alike, with the string unquoted ("TLCGet(foo) was undefined."): the engine stops at
it (`TLCGet of a key TLC doesn't know`) for that evaluator to word. Of the keys TLC knows, the
engine still stops at those its search doesn't keep, as "revision", whose record names the
jar's build (see "TLCEvalDefinition, system properties, "exit", and TLCGet of the run").

TLCExt's `ToTrace` accepts TLC's actual `CounterExample` record subtype, rather than a record
with the same fields. Aliases retain that origin; record reconstruction, a successful field
update, and `TLCEval` conversion produce ordinary values. The trace evaluator retains this
distinction and reports TLC's argument error for ordinary records and functions. A value whose
origin was erased by engine transfer still declines. The `to-trace-origin-*` startup fixtures
record these cases against TLC at d8fb231, including genuine empty and violating traces. The
engine, which computes no CounterExample (it declines `CounterExample`), stops at ToTrace of any
value it computes, after the argument, with `ToTrace of a value that isn't a CounterExample`, a
failure the trace evaluator words (or declines where it computes a trace, as for a value whose
origin it doesn't keep).

Two inherited symmetry-warning differences remain: for a violation with an ALIAS that builds
a function and `SYMMETRY Permutations({})` or `Permutations({a})`, warning2300 prints a blank
set where TLC prints `{}` or `{a}`. The violation and trace otherwise agree. Main and the native checker
have the same difference at one and four workers; this is separate from CounterExample subtype
handling.

A constant definition whose body is directly `PrintT` may be retried after a startup failure even
when its argument may be lazy: `PrintT` returns a boolean, and the engine keeps no value only when
it failed before it set any register. The trace evaluator independently confirms the TLC failure
before the result is reported. Definitions that may read state or depend on a substitute,
and engine limits such as an attempt to enumerate `Int`, remain declines unless the paragraph below
applies. The trace evaluator follows `TLC.Print` and `PrintT` deep-normalizing their arguments before
printing (`deep_normalize_print`): each set enumeration TLC holds unnormalized and reaches through
tuples, records, function values, lazy set operands, set-of-functions/records/tuples factors,
SUBSET, UNION, a filter's base and a lazy function constructor's domain and EXCEPTs is sorted in
place, so a later membership test searches it with `compareTo` as TLC does rather than in written
order with `equals`; a set TLC fails to sort fails there, inside the Java method's error. It declines
a print that reaches such a set through a function constructor TLC may hold built or a function
domain of two or more keys. With that, a startup PrintT no longer needs the earlier guard against
differences whose tested set may be held in written order. The startup fixtures record the
lazy-print failures and bound values against TLC.

A retried constant definition that fails as TLC starts after it printed or drew (`RandomElement({})`
draws before it indexes its empty vector) keeps no value either: TLC swallows the failure
(`processConstantDefns`) and evaluates the definition again at each use, which prints and draws
again in the same order, from the generator the engine and the trace evaluator both follow, and
fails again. The search's prints of such a definition must be TLC's: where the engine stopped at
a limit of its own before a print TLC makes, as building `1..100000000` or `1..2147483647` for
`PrintT(1..100000000) /\ 1 \div 0 = 1`, TLC prints the interval as it starts and again where the
definition is used, where the binary printed it once; the evaluator of failures counts the prints
it makes of the definition before it fails, and declines where they aren't as many as the
search's ("a startup definition the search found failing that prints otherwise here"; main
declined these). Such a definition still declines, "a definition TLC computes at startup that fails
there", where it set a register (TLC has made no checker whose registers TLCSet sets as it
processes the spec). TLC computes every constant definition of no argument, used or not, and
evaluates the failing one again inside another that names it, as written or through the
definitions it names, as it starts, printing and drawing a further time (`Bad == IF PrintT(1) THEN
CHOOSE x \in {} : TRUE ELSE 0` with `Test == Bad = 0` prints three times before the assumption
fails; `Bad == PrintT("p") /\ 1 \div 0 = 0` with an unused `Use == Bad` prints twice and finds no
error). The front end lists those others, used or not, where TLC computes them among the startup
definitions (`Startup::dependents`), and the engine evaluates each there where a definition it
names failed, keeping what it prints and draws as it fails again; it computes nothing of one that
evaluates no failed definition, as `Use == TRUE \/ Bad`. Such a dependent still declines where it
computes with an effect (a failed definition that computed this time, as one that draws), fails
at a limit of the engine's or after it set a register, or may hold its value lazy (as a filter
of `Nat`), whose parts TLC may evaluate elsewhere or never. A dependent that fails there, which
the configuration names as an invariant, a constraint, an action constraint, the initial predicate,
the next-state relation or the specification (`Bad == PrintT(1) /\ 1 \div 0 = 1`, `Inv == Bad`,
`INVARIANT Inv`), declines too ("a definition TLC computes at startup that fails there, named in
the configuration"): TLC keeps it as an operator, which `processConfigInvariants` and its kin take
without evaluating it again, where the engine evaluated it once more and printed again (main
declined these).

TLC keeps no value of a startup definition that failed as it started, so every use evaluates it
again, with its prints and draws, even after a use at which it computed: `D == LET r ==
RandomElement(1..1000) IN PrintT(<<"d", r>>) /\ (r = 731 => 1 \div 0 = 1)` fails at its first draw
and then computes, and `Test == PrintT(D)`, `Other == PrintT(D)` print D's tuple at each. The
engine kept the value of the first use that computed it, and printed D once for both (main
declined these). It now marks such a definition's slot as one it evaluates again at every use
(`Machine::constant_once`, `RETRIED_ONCE`).

A name TLC binds to a `LazyValue` of such a definition reads it once, though: a LET definition,
an operator's argument or an INSTANCE's substitute (`LET p == D IN PrintT(p) /\ PrintT(p)`,
`F(D)` with `F(a) == PrintT(a) /\ PrintT(a)`, `LET p == D IN PrintT(<<p, p>>)`) evaluates D at
its first read and keeps that value for the others (`LazyValue.getValue`), so TLC prints D's
tuple once there. The engine evaluated D at each read and printed it twice (main declined these).
In a constant definition TLC computes as it starts, a LET definition or an argument named more
than once whose expression may reach a startup definition with effects is now kept from its
first use (`Argument::reaches_startup`, `read_once`), as one that prints is (a bound variable of
a quantifier, CHOOSE, set or function constructor within the expression holds a value and
reaches none: `T == LET g == [i \in 1..2 |-> i] IN DOMAIN [g EXCEPT ![1] = 0]`, beside a startup
definition that may warn, answers as main does, `let-domain-of-except-unused-constant-definition`); elsewhere such a read
that reaches a failed startup definition declines ("a definition that failed as TLC started,
read through a name TLC binds once and the body reads again", `Machine::retried_reads`). An
INSTANCE's substitute naming such a definition, read twice in one copy (`I == INSTANCE OD WITH
c <- D` with `C3 == PrintT(c) /\ PrintT(c)`), where D draws, declines where D's computation as TLC
starts fails after a print or a draw (`Definition::NAMED_AT_STARTUP`, "a definition TLC computes
at startup that fails there"); where it doesn't fail, every read gives the value TLC kept, as the
engine's does, and it answers (see the drawing substitutes below).

In the initial predicate and the next-state relation, which TLC walks with `getInitStates` and
`getNextStates`, a LET definition or an argument read as a conjunct is not read through its
`LazyValue`'s cache: `getInitStatesAppl` and `getNextStates` find no value cached and evaluate its
expression again at each read, without keeping it, and each application of an operator binds its
own. So `Init == LET p == D IN p /\ p /\ x = 0` prints `<<"d", 731>>` (as TLC starts), then
`<<"d", 919>>` and `<<"d", 680>>`, where the binary printed 919 twice, and `Op(a) == a /\ x = 0`
with `Init == Op(D) /\ Op(D)`, where D fails at a draw of 680, failed in TLC where the binary
reported no error (main declined these). The walk now compiles such a name whose expression
reads no state and may reach a startup definition as the name, and in the initial predicate and
the actions it walks (`Context::is_walked`) a read of a LET definition or an argument whose
expression may reach a startup definition declines where it evaluated a definition that failed as
TLC started again with an effect, a print, a draw or a register's write ("a definition that failed
as TLC started, evaluated again with effects through a name TLC may evaluate at each read",
`guard_retried_effects`); a read that fails there fails as TLC's does. A constant definition, an
assumption or an invariant, which TLC evaluates through `LazyValue`s that keep the value, reads
such a name once, as before (`F(D)` with `F(a) == PrintT(a) /\ PrintT(a)`). A next-state
relation that reads such a name where it is only evaluated (`x' = F(D)`) declines too, though TLC
keeps the value there.

A startup definition the engine computed is read as the value it kept wherever it is used, as TLC
reads the deep-normalized value `processConstantDefns` kept: sizing it, enumerating it, testing an
element of it or reading an interval's bounds evaluates nothing of its body again. The engine held
such a definition with the parts a parent may evaluate in place of its value (its reference, its
elements' references, its membership test, its filter, an interval's bounds), which evaluated the
body again: `Cardinality(S)` of `S == {Print("e", 1), 70}` printed twice where TLC prints once,
in an assumption, the initial predicate, a step, an invariant and a property, and `S == {x \in
{Print("e", 1), 2, 3} : x > 1}` printed once more for each `Cardinality(S)` (main matched the
first and declined the second). A definition whose body may have an effect now keeps only its
value. Whether a body may have an effect now also looks into a filter's set, which the IR's
children of a filter leave out.

`processConstantDefns` computes a constant definition that applies a Json operator, whose Java
method has no minimum level (`Json.toJson`), and swallows its failure, evaluating it again at its
use, where the front end takes the Json operators as of state level, so the engine computed such
a definition only where it is used, each time: `Test == PrintT("x") /\ ToJson(Nat) = ""` printed
`"x"` once where TLC prints it twice before the 2154 failure, and `T == PrintT("x") /\ ToJson(1) =
"1"` used twice printed it twice where TLC prints it once (main declined these). Such a definition
that converts a value with `ToJson`, `ToJsonArray` or `ToJsonObject` and prints, draws or sets a
register declines ("a constant definition with effects applying a Json operator, which TLC
computes as it starts"); one that reads or writes a JSON file is evaluated at each use, as main
does (see "Known wrong outputs"). This gives up a definition that converts a value that can't fail
(`Test == PrintT(ToJson(1))`), which an earlier build answered: it matched only where nothing
else prints between TLC's startup and the definition's one use, as TLC prints its effects at
startup and the engine at the use; main declines these.

Where the trace evaluator doesn't follow TLC's generator, a `RandomElement` of an interval with no
element fails whatever the generator gives (`IntervalValue.randomElement` checks its bounds), and
so does one of the empty set written `{}` in place, whose vector has no room
(`SetEnumValue.randomElement` indexes it with `ValueVec.elementAt`, which checks no bound), so the
evaluator words those failures, also where such a set is the first with no element that a draw
from a set of functions, records or tuples reaches as `TLC.RandomElement` draws each part in turn
(`[{1} -> {}]`, `[a : {}, b : S]`). Any other set with no element declines (`a random draw where
the evaluator doesn't follow TLC's generator`): TLC builds some in a vector with room
(`SetPredValue.toSetEnum` of `{x \in S : P}` that keeps nothing), where the draw gives null rather
than failing, and fails later, writes null into a state, or not at all. A draw that gives an
element still declines.

As TLC processes the spec it has made no checker or simulator yet (`TLCGlobals.mainChecker` is
null), so TLCExt's `TLCGetOrDefault` finds no register for any key there and gives the default,
even for a negative index, which a checker's worker rejects with an
ArrayIndexOutOfBoundsException. The engine and the trace evaluator give the default for a
substitute or a constant definition they compute as TLC starts; elsewhere a negative index still
declines (`TLCGetOrDefault of a negative number`). TLCGetOrDefault is a Java method, whose key and
default TLC evaluates once each, in order, before it runs, so a print in either prints where TLC
computes the call (`Print` declines in a LET operator's body or TLCGetAndSet's value, as before).

A startup failure that is the engine's own limit, such as enumerating `Nat`, says nothing of whether
or how TLC fails. A retried definition that hits one is now handed to the trace evaluator like any
other swallowed failure: `confirm_startup` evaluates the startup as TLC does and declines where the
evaluator computes the definition, fails without TLC's message, or fails after an effect. A
definition kept only for its warnings (an EXCEPT's, `STARTUP_WARNING_ONLY`) that hits one before
any effect or warning is kept unvalued without counting as failed (`limited_startup`): TLC
swallows its failure, or computes it and keeps the value, and the engine evaluates it again at
each use, meeting its limit there again, either way. The confirmation declines only where TLC
warns, prints or has an effect as it starts on it, or where the evaluator fails in a way it
can't follow, past which TLC may warn ("a startup definition the search failed at a limit of
that warns or prints here", "... that the evaluator can't follow"). So `Test == [<<1, 2>> EXCEPT
![1] = Cardinality(Nat)][2] = 2` words TLC's failure where it is used, as main did under
`ASSUME` and now in every context (365 of 365 probes match, 46 of them main's matches the
integration had lost); `[<<1, 2>> EXCEPT ![1] = SUBSET Nat][2] = 2`, with `Nat \X {1}` or
`Seq(Nat)` in its place, which TLC computes lazily, answers where it is used as main did; and
one that warned first, `[<<1, 2>> EXCEPT ![3] = 1, ![1] = Cardinality(Nat)]`, still declines
(`except-limit-startup-*` fixtures). Where the definition is a
`PrintT` of an effect-free argument (`is_pure_print`) that
the engine can't compute, at a limit of its own or at a failure of a value it computes where TLC
keeps it lazy, but the trace evaluator, evaluating it as TLC starts, computes to TRUE with that
one print last and a deep normalization it follows (`computes_startup_print`), the engine
records an unworded print that only the trace evaluator words, and its startup must compute that
print again or the model declines. So `PrintT({} \X SetToBag({1}))` prints `{}` and
`PrintT(SUBSET <<>>)` prints `{{}}` where the engine stopped on a value that isn't a set; a print
whose normalization the evaluator doesn't follow still declines. The argument may hold a LAMBDA
(`SortSeq(s, LAMBDA p, q : p < q)`, or one in the body of a function TLC keeps lazy and prints
unbuilt), and the evaluator's EXCEPT warnings (2144) as it computes the argument print before the
print, in place of those the engine printed before it stopped: `PrintT(DOMAIN [[x \in Nat |-> x]
EXCEPT ![-1] = 1] \cap ...)` warns once and prints, as TLC does. Before, both declined ("a startup
definition the search found failing that computes"; `startup-print-*` startup_checks fixtures). A function
over an interval wider than the evaluator builds an interval to declines in the evaluator, since TLC
may keep it lazy.

A retried startup definition the engine finds failing may stop at a value TLC keeps lazy before a
print TLC makes: `Test == PrintT(1..2147483647) /\ 1 \div 0 = 1` stops the engine at the interval
too large to build, before PrintT, and `PrintT(Seq(S)) /\ "a" \in S` at `Seq(S)`, where TLC prints
the `IntervalValue` or `SetOfSeqValue` as it starts, swallows the failure, and prints it again at
each use, where the engine fails before the print again. The search hands the confirmation how many
prints each startup definition made before it failed, and whether it drew, and the trace
evaluator's startup must print and draw as much before the failure it confirms ("a startup
definition the search found failing that prints or draws here before it fails as the search
didn't"); main declined these ("a definition TLC computes at startup that fails there"), and the
search had printed the interval once, or not at all, where TLC prints it two or three times. A
print of a value the engine builds (`PrintT(1..1000001)`, `PrintT(1)` before
`Cardinality(0..2147483647) = 0`) still answers.

A constant-level definition that fails as TLC starts and that the configuration names as an
INVARIANT, CONSTRAINT or ACTION_CONSTRAINT is the OpDefNode `processConstantDefns` kept, which
`processConfigInvariants` and its kin take as an action without evaluating it again; the engine
no longer evaluates such a predicate at startup (for the constant-invariant check), which printed
`Inv == PrintT(1) /\ 1 \div 0 = 1` once more than TLC (`*-named-print-then-fails` fixtures). A
failed definition that is a conjunct of the SPECIFICATION still declines, and so does one that
printed or drew as it failed and that the configuration names as INIT, NEXT or SPECIFICATION
("a definition TLC computes at startup that prints or draws and fails there, named as the
initial predicate, ..."): TLC heads the nested positions of its report with the conjunct that
printed, which the evaluator of failures leaves out (`init-named-print-then-fails`).

`processConstantDefns` evaluates the definition a configuration substitutes for a declared
constant (`CONSTANT C <- D`) and swallows only the EvalException or TLCRuntimeException it
throws: a recursion without end overflows TLC's stack and ends the startup with
EC.SYSTEM_STACK_OVERFLOW (exit 255), where the engine evaluated a substitute of constant level
only where it is read and printed a deadlock trace, or a clean run, as main does. The front end
lists each such 0-ary substitute that may recurse (a RECURSIVE operator or a recursive function,
its own or one it reaches: `Startup::recursive_substitutes`), and the engine evaluates it as it
starts, keeping nothing of it, and declines where it nests more than 50 recursive calls
("a substitute whose recursion may overflow TLC's stack as it starts", `substitute-endless-*`,
`substitute-deep-ending-recursion` and `substitute-ending-recursion-through-operators`
fixtures); a recursion that ends sooner, as `D == Fact(5)`, answers as before. A recursion that
ends but runs deep overflows TLC's stack all the same, at a depth that depends on the body, not on
the number of calls: under TLC's 2 MB thread stack, `RECURSIVE S(_)` with `S(n) == IF n = 0 THEN
0 ELSE S(n - 1) + 1` evaluates at `S(900)` and overflows at `S(1000)`, `F[i \in Nat]` of the same
shape overflows at `F[800]`, a body of a LET, CHOOSE and CASE at 380, and one that reaches the
next call through a chain of 8 operators at 150, of 20 at 64, of 24 at 55 and of 32 at 40, where
the engine, main and the base before this bound all printed a clean run. 50 calls keeps every
probed shape but the last: **known wrong**, a substitute whose recursion ends within 50 calls but
whose body reaches the next call through about 26 or more operators prints a clean run where TLC
overflows its stack (exit 255); `D == S(40)` of the 32-operator chain is one. The engine has no
measure of TLC's stack. Reporting TLC's 1005 there, as for a recursion without end in a state,
would win the declines, but not this. No run of the corpus has a substitute that recurses.

The trace evaluator words more of the failures TLC meets in startup definitions. A function TLC keeps
lazy over a set its modules override (`[x \in Nat |-> e]`) that a `TupleValue` equates or compares
with is made a tuple (`toTuple`, "the set S must be enumerable"); a function, record or model value
builds it (`toFcnRcd`, "the number of elements in the overridden value"); a function of unknown class
declines. That failure is no longer one the failed-startup confirmation treats as unsure, but in a
membership in a set of functions or records (see the failed startup definition evaluated again over
`[x \in Nat |-> x]` below).
`~`, `=>` and `<=>` on a non-boolean give `Tool`'s OPCODE_lnot, OPCODE_implies and OPCODE_equiv
messages with the operand's kind and the expression's place; a kind the evaluator doesn't know
declines. A `\subseteq` takes its left operand's elements as TLC's Enumerators stream them and stops at
the first its right operand lacks (`EnumerableValue.isSubsetEq`, `sets::stream_until`). A lazy UNION all
of whose sets are set enumerations or intervals, all empty but one held sorted, counts as settled.
A printed difference of a set of functions or records built from literals, whose tested set is
also built afresh from literals with builtin set and integer operations, filters and maps
(`is_fresh_literal`), words TLC's function and record comparison failures. A function TLC built
(`FcnRcdValue`) with a single key is searched with `equals`, as `selectBinarySearch` searches
fewer than 32 keys linearly, whatever order the evaluator doesn't know it holds them in.
Where that key's `equals` fails and the key isn't an integer or a string, the search declines
("a single-key function whose key fails to equal the argument"): TLC's key built from a tuple, set
or record literal, even `{}`, has its source, and TLC reports a FingerprintException (2147 and a
Fingerprint Stack Trace ending at the key) that the evaluator doesn't word.
The failed-startup confirmation no longer treats every failure inside a function constructor as
unsure: `Tool`'s OPCODE_fc evaluates the domains eagerly, in order, so a failure in a domain, the
frame right after the constructor's being one of its bound sets, is TLC's; one in the body, which
TLC may keep lazy, still declines.

The replay checks TLC's `Enumerable` interface before computing a subset relation, choosing an
element, or counting a set. A subset relation evaluates both operands before checking the left
one; CHOOSE checks its bound before evaluating the predicate. Functions, records, tuples and
scalars therefore receive TLC's non-enumerable diagnostics instead of a generic set-type decline.
The subset check belongs to `Tool`, so it keeps the outer expression's call stack rather than
attributing a FingerprintException to the left value's source. The `set-diagnostic-*` startup
fixtures record these errors and their operand effects against TLC at d8fb231. The existing
startup uncertainty guards still decline a failure whose lazy evaluation or effects the replay
cannot place as TLC does.

Where the search stops at a value TLC can't enumerate or count where the engine can't either
(`is_replayed_limit`: enumerating Nat, Int, STRING, Seq(S) or another infinite set, counting
one, an interval or power set too large to build, Warshall of a non-pair, IsFiniteSet of a set
TLC may fail to tell finite), it notes the failure as it notes one TLC reports, and the
evaluator of failures evaluates the model again: it words TLC's error where TLC fails there,
placing a failure of TLC's enumerator of a set among the values whose `elements` it passes
through (their sources head the FingerprintException), and finds none, which declines, where TLC
doesn't fail or the evaluator can't place the failure (`a set TLC fails to enumerate in a method
the evaluator doesn't place`). A `\subseteq` places it as its left operand's `isSubsetEq` throws it
on (`({1} \cup 1) \subseteq {1}`), unless that operand is a power set, whose `isSubsetEq` may
compare its base instead. A power set whose base TLC can't count (Nat, Int, STRING, Seq(S),
an interval past 2^31 - 1 elements, or the power set of one) fails as TLC sizes the base in the
power set's `elements` (`SubsetValue.elementsNormalized`, `size`): the power set's source joins
the FingerprintException, after those of the sets that enumerate it (a union, a difference, a
UNION, a set of functions, records or tuples, a set enumeration that compares with it) and before
that of an overridden base that has one; a comparison that enumerates such a power set, as
normalizing `{SUBSET Nat, {1}}` does, adds it after the operands it compares (`compareTo` calls
`toSetEnum`, which sizes it). Of several bounds, the first whose set isn't an
enumeration or interval fails (`Tool.contexts`). Where a node that gives a value a source returned
a value of that chain, as DOMAIN of a function constructor returns its domain
(`CallStackTool.setSource` replaces its source), or where such a node returned an interval TLC
counts in its own method, the failure declines. So does a failure to enumerate a set through a
value such a node returned, as the domain of `[{} \cup (Nat \ {0}) -> {1}]` or the bound of
`\E x \in {} \cup (Nat \ {0}) : TRUE`. A union whose empty set enumeration or interval
receiver returns the other operand itself (`SetEnumValue.cup`, `IntervalValue.cup`) gives it the
union's source, which the replay follows. Nat, Int, Real and STRING are each one object TLC
shares wherever the spec names it, so a source such a union or DOMAIN gives one is its source
wherever its own method fails next, as in `1 \in ({} \cup Nat) /\ Nat = 1`; the replay keeps one
source for each, the last node's. An interval such a node returns, as `{} \cup (1..2)` or
DOMAIN of a tuple, which the replay holds without an address, has that node's source where the
node is the operand whose method fails (see the known wrong output below for one passed on). Enumerating an interval too large to build declines there too (`an interval too large to
build that TLC may walk`): TLC walks it without counting it (`IntervalValue.elements`) in
`\subseteq`, a power set's `member`, a filter or a union, where it answers or fails otherwise.
`TLCEval` enumerates a set whose operand reads the state as it does a constant one, so a failure
there is the Java method's. `IsFiniteSet(Seq(S))` is computed as `SeqValue.isFinite` does: S
finite and empty, asking S whether it is empty only where it is finite. `IsFiniteSet(UNION S)` is
computed as `UnionValue.isFinite` does, asking each set S holds, where S holds finite sets or Nat,
Int or STRING alone, or where S is the power set of a base of at most 20 elements that all compare
(a set the store holds, or a power set, set of functions, set of records or product of such sets):
`SubsetValue.elementsNormalized` enumerates its subsets, each finite, comparing nothing that fails,
so `IsFiniteSet(UNION SUBSET {1, 2})` and `UNION (SUBSET {})` are TRUE (the
`union-of-power-set-is-finite` startup fixture). Any other S stops for the evaluator of failures
(`IsFiniteSet of a set TLC may fail to tell finite`), as TLC's sort of S may fail first; a larger
base declines too, whose 2^n subsets TLC asks one by one.

Some sets TLC keeps lazy are compared, counted or written without enumerating them, which the
engine follows. `S = T` and `S # T` where either may be one the engine only tests compare the sets'
references as TLC's `equals` of S does: Nat and Int by their modules' `compareTo`, and two sets of
functions, records or tuples, or two power sets, by emptiness and then by the sets they're built of
(`SetOfFcnsValue.equals`, `SetOfRcdsValue.equals`, `SetOfTuplesValue.equals`,
`SubsetValue.equals`); a union with an empty set enumeration or interval is the other set
(`Reducible.cup`). Any other pair, a part that fails or that the engine can't compare (such as
`{"a"}` with `{1}`), and an operand that may have an effect or is an operator parameter, compare as
before, stopping for the evaluator of failures. `Seq(S) = T` compares with another Seq(S') by the
ranges, and is unequal to a model value (`UserValue.equals`, `Sequences.compareTo`); any other T
stops for the evaluator of failures (`compared Seq(S) with a non-overridden value`), and ranges the
engine doesn't hold as sets decline (`comparing Seq(S) with a value the engine doesn't`). Two
intervals compare by `IntervalValue.equals` (an empty receiver equals only an empty interval, whose
elements TLC counts then, and fails counting past 2^31 - 1 elements, where the comparison stops as
before) and `a..b \subseteq c..d` by `IntervalValue.isSubsetEq`, which walks a..b against c..d's
bounds without counting it. `S \cap a..b` and `S \ a..b` of a set enumeration S test S's integers
against the bounds (`SetEnumValue.cap`, `diff`, `IntervalValue.member`) without building a..b; an S
that holds another value, or an operand with an effect, is computed as before. The trace
evaluator's interval comparison counts the same intervals, so `(0..2147483647) = (1..2)` fails as
TLC does. `Cardinality(a..b)` counts the interval without building it (`IntervalValue.size`), and
`Cardinality(SUBSET S)` is 2^n for a normalized base of n elements, failing from 31 on
(`SubsetValue.size`). `CHOOSE s \in SUBSET S : P` over a normalized base of more than 20 elements
takes the subsets in TLC's normalized order without building the power set
(`SubsetValue.elementsNormalized`: by size, then by the positions of their elements in S); the
trace evaluator still builds it, so a trace through one declines. `ToString`, `Print` and `PrintT`
write Nat, Int and STRING by their names. `TLCEval` leaves Nat, Int and STRING as they are
(`UserValue.toSetEnum` is null) and stops at any other set the engine only tests where TLCEval
would enumerate it (`toSetEnum`), for the evaluator of failures to word TLC's failure; one whose
operand may have an effect declines (`TLCEval of a set TLC may not enumerate`). The trace evaluator
enumerates such a set where TLCEval does (`TLCEval.convert`), where its operand has no effect, and
reports a failure there as the Java method's (so `3 \in TLCEval({n \in Nat : n > 2})` fails, where
it passed before), keeping the lazy set where the enumeration succeeds. It checks `RandomSubset`'s
arguments before it draws, as `Randomization.RandomSubset` does: a count that isn't an integer, and
a set that isn't a finite `EnumerableValue` (a failure of `isFinite` the Java method's), fail;
where anything printed before, which TLC shows twice for a constant definition it evaluates as it
starts and again where it is used, it declines as before (`a random draw where the evaluator
doesn't follow TLC's generator`). Randomization's Java `RandomSubset` has no minimum level
(`MethodValue.get`), so `processConstantDefns` computes a constant definition that draws with it
as TLC starts, and every state reads the value it drew: where the pinned Randomization class is
the one TLC loads, the front end counts it constant and effectful, and the engine computes such a
definition with the startup's generator. The engine had counted it state-level and drew it again
in each state, from the generator seeded with the state's fingerprint: `Test == RandomSubset(3,
1..20) # {9, 11, 18}` under `Next == s' = Test` reported "No error has been found" where TLC
reports the invariant violated (as `main` still does). TLC evaluates a startup definition with a
next state (`evalConstantDefn` passes `TLCState.Empty`), so the `LazyValue` it binds a LET's
definition or an operator's argument to keeps the value of its first use (`Tool.evalAppl`,
`LazyValue.getValue`): a draw or a print there runs once, where the name is first used, and not at
all where it isn't used. The engine keeps such a name with effects in a slot from its first use to
the end of the LET or the call (`Argument::once_slot`), where every use is one it evaluates as TLC
does; PrintT prints such a name bound to a direct draw, or a tuple of them, as it prints the draw.
`S == LET T == RandomSubset(1, 1..9) IN T \cup T` draws once, and `SingletonOf(RandomSubset(1,
1..3), 1..3)`, whose parameter the body names three times, draws once. A subset test of integers
against `a..b` compares each with the bounds (`IntervalValue.member`) where the engine had built the
interval, which stopped `RandomSubset(1, 1..MaxInt) \subseteq 1..MaxInt`. A startup definition the
engine can't compile, such as `PrintT(F(2))` with `F(k) == RandomSubset(k, 1..10)`, `PrintT(LET z ==
RandomSubset(2, 1..20) IN z)` (`unsupported: RandomSubset`) or `LET T == RandomSubset(2, 1..1000) IN
PrintT(<<T>>)` ("Print where TLC evaluates it otherwise"), the engine leaves to the trace evaluator
where the first assumption names it, itself or through the definitions it names, and nothing else
reads it (`is_left_to_reporter`): what the engine compiles names it and fails to compile as it
does, and an ALIAS, a POSTCONDITION or a VIEW, which the trace evaluator computes, declines it.
The trace evaluator computes the startup as TLC does up to the definition and again past it
(`Rebuilder::compute_startup_until`); where it made as many prints before it as the engine did,
from the same generator's state, and computes it without failing, warning or setting a register,
the engine prints as many lines as it does there, which the trace evaluator words, and goes on from
the generator's state it leaves (`Reporter::computes_left_startup`). The first assumption, which
fails to compile as it names the definition, goes to the trace evaluator, which reads the value it
kept there. So `PrintT(LET z == RandomSubset(2, 1..20) IN z)`, `PrintT(CHOOSE s \in
{RandomSubset(2, 1..9)} : TRUE)`, `PrintT({RandomSubset(1, 1..9)})`, `PrintT(RandomSubset(1, 1..9)
\cup {})`, `PrintT(Cardinality(RandomSubset(2, 1..9)))` and `S == LET T == RandomSubset(2, 1..1000)
IN [x \in 1..2 |-> T]` printed answer in an assumption, where `main` matched too, and so do such
definitions beside others that draw or print before or after them as TLC starts, which `main`
declined (`A == PrintT(RandomElement(1..100))` before, or `Z == PrintT(RandomElement(1..100))`
after). Still declined: one the first assumption
doesn't name, as where the spec's own `ASSUME PrintT(RandomElement(1..9))` comes first, and one the
trace evaluator fails on (`... /\ 1 \div 0 = 1`, which TLC swallows and computes again at each use)
or that sets a register, with the reason the engine didn't compile it (`unsupported:
RandomSubset`), or, where the engine kept no such reason, "a startup definition the engine doesn't
compile, which the trace evaluator doesn't compute as TLC starts". `main` matches `ASSUME PrintT(LET z == RandomSubset(2, 1..20) IN z)` before
`ASSUME Test` of that same expression only by chance: it makes TLC's two draws in the other order,
and prints the same text for each. In the initial predicate, an action, an invariant or a property,
which read such a definition, the engine fails to compile it as before and declines (as `main`
does). The engine's stop at a count that
isn't a natural number goes to the evaluator of failures, which words `Randomization.RandomSubset`'s
argument error.

A LET's operator with parameters is no `LazyValue`: TLC evaluates its body anew at each
application, as it does a global operator's (`Tool.evalAppl`), so it prints at each one, and the
engine compiles it where it may print as it compiles a global operator, however often the LET
applies it (`Test == LET f(z) == P(z, z) IN f(1) + f(1) = 2` with `P(m, v) == IF PrintT(m) THEN v
ELSE v` prints 1 twice), in the initial predicate, an action, an invariant and a property too. A
recursive one still prints only where the LET names it once. The check of a startup print that may
hold a set TLC fails to size (`may_write_unsized`) follows such an operator into its body where it
is applied, with its parameters holding what the arguments may, as it follows a global operator's,
where the LET only applies it.

The order in which TLC computes the startup definitions shows wherever two of them draw or print.
`processConstantDefns` takes the modules of files in the order SANY finishes them, each module's
own definitions (`getOpDefs`) and then, recursively, its inner modules (`getInnerModules`), which
its module table doesn't hold: an inner module's definitions come after those of the module that
holds it, where the front end had taken the inner module first, as SANY finishes it. With
`---- MODULE Inner ---- IR == RandomSubset(2, 1..20) ====` never instantiated and `Test ==
RandomSubset(2, 1..20) # {9, 11}`, TLC gives Test the first draw and finds the assumption false;
the engine gave it to IR and reported "No error has been found" (and printed the draws of
`IR == PrintT(RandomElement(1..20))` and of the root's in the wrong order). Two
cases still decline. TLC takes a module's inner modules in the order of its context's Hashtable
(`Context.getModDefs`), not the source's, so effects at startup in two inner modules of one module
decline (`effects at startup in two inner modules of a module`), as does a substitution whose
target has a module-scoped value beside two such inner modules, whose value depends on which
definitions TLC computes first (`a substitution whose target has a module-scoped value, beside two
inner modules of a module`). An unnamed INSTANCE of a module of
a file without parameters puts that module's own `OpDefNode`s in the instantiating module: TLC
computes each with the module, which SANY finishes first, and `lookup` finds its value when it meets
it again, so the front end's one definition is TLC's. A named INSTANCE (`I!D`), or an INSTANCE of a
module with parameters, copies each definition into a node of its own, which TLC computes in the
instantiating module, at the INSTANCE's place among its definitions, with its own draws and prints;
the copy's body names the module's own definitions, whose values it reads. The front end makes such
a copy a definition of its own, which the startup computes there, as it already did for a copy with
substitutions; the module's own definitions TLC computes only where the module has no parameters
(`ModuleNode.processConstantDefns`). With `A == PrintT(<<"A", RandomElement(1..1000)>>)`, `I ==
INSTANCE Inner`, `B == ...` and `One` and `Two` that print draws in `Inner`, TLC prints `one` and
`two`, then `A`, `one`, `two` and `B`, and the assumptions last; with `INSTANCE Inner` unnamed,
`one` and `two`, `A` and `B`. Copies the front end doesn't order as TLC does still decline (`an
INSTANCE of a module with a definition TLC computes as it starts with effects`): those of an
INSTANCE of an inner module without parameters, or of an INSTANCE in a LET, and the definitions of
a module with parameters another module extends, which the front end computes. Of an inner module
with parameters TLC computes only the copies, in the instantiating module's order as for any other
module with parameters (the module's own definitions `ModuleNode.processConstantDefns` skips), so
`I == INSTANCE Inner WITH K <- 2` with `IR == RandomSubset(K, 1..20)` in `Inner` answers: TLC
draws `I!IR` once as it starts, and `PrintT(I!IR) /\ PrintT(I!IR)` prints the same set twice. An unnamed LOCAL INSTANCE of a
module without parameters is not a share either: SANY's `Generator.generateInstance` makes a new
OpDefNode of each definition (`if (localness)`), which TLC computes again in the instantiating
module, so it declines alike, except where the instantiating module already binds each of those
names to the module's own definitions by an earlier EXTENDS or INSTANCE of it, where
`SymbolTable.addSymbol` keeps them and drops the copies (`local-instance-*` startup fixtures).
`main`, which draws a RandomSubset
where the evaluation of the assumption reaches it, matched such a spec only where that order is the
definitions' order; it is wrong once a definition that draws comes first, as for `A ==
RandomSubset(2, 1..20)  I == INSTANCE Inner  Test == PrintT(I!IR) /\ PrintT(A)`. Two suite runs that
this decline cost now match: `tlc/standard/randomization/subset_cardinality#assume` (a LET's draw
used twice) and `ModuleSemanticsAssumeTest/ModuleSemanticsAssume` (an unnamed INSTANCE of a module
whose definitions draw, an argument drawn and named three times, and `RandomSubset(-1, {1, 2})`,
which fails as TLC starts and again in an AssertError, where the evaluator of failures follows it
within a call stack of its own). Neither shows what is drawn, as the first prints nothing and the
second is exit-only, and their assumptions hold whatever is drawn, so `main` answered them right. An
earlier entry here held that `main` matched them only by the order, with `S == LET T ==
RandomSubset(1, 1..9) IN T \cup T` after `ASSUME PrintT(RandomSubset(1, 1..9))` printing `{3}` then
`{1}` in TLC, and `PrintT(<<One, Two>>)` of an unnamed INSTANCE printing `<<{2}, {2, 3}>>` on
`main`; neither is so. With `-seed 4` TLC prints `{1}` then `{3}` (it computes `S`, and the startup
definition `Test == PrintT(S)` prints its draw, before the assumption draws), as `main` does, and
both print `<<{2}, {3, 7}>>`. `main` is wrong on near specs, where TLC's order of the draws isn't
the assumptions': with `S == LET T == RandomSubset(2, 1..1000) IN <<T>>` and an `ASSUME
PrintT(<<"asm", RandomSubset(2, 1..1000)>>)` before `Test == PrintT(<<S, RandomSubset(2,
1..1000)>>)`, TLC prints Test's tuple first, `main` the assumption's (the engine declines there, as
PrintT of a tuple holding S isn't one it prints); and with `PrintT(<<Two, One>>)` in place of
`PrintT(<<One, Two>>)`, `main` draws `Two` first.

Set maps and filters that TLC builds into a fresh `ValueVec` enforce its default 1,000,000
emitted-element bound after evaluating each image or predicate, before insertion and deduplication.
A constant image still reaches the bound; a FALSE filter over a larger input does not. A fused
filter cardinality checks that emitted count, then counts distinct kept elements when the lazy
input can stream duplicates. A filter
TLC keeps lazy receives the bound when it is materialized, including for a normalized CHOOSE or
quantifier, while membership can test one element without materializing it. The replay preserves
the empty call stack of a raw `WrongInvocationException` and the Java-method wrapper when
`Cardinality` materializes the filter. The `set-bound-*` fixtures record these distinctions and
large-set controls against TLC at d8fb231. Lazy predicates with effects and startup
failures whose evaluation the replay cannot place still decline.

Nested lazy filters check that each base is Enumerable before evaluating a predicate. A bad
base keeps the filter's own enumeration diagnostic, including inside PrintT or Cardinality;
Cardinality wraps runtime materialization failures as Java-method errors and preserves
EvalException failures. A nullary definition of constant level under TLC's `getLevelBound`
analysis declines if it prints before this enumeration failure while its startup retry is
unmodeled. Inline assumptions, cached bases,
stateful helpers and parameterized helpers keep their matching print behavior. The
`filter-base-*` fixtures pin these diagnostics and ignored effects.

Speculative filter evaluation records conversion and thunk-cache changes in nested
transactions. If it converts a filter, replay restores the original cache objects and
memo state and discards the speculative result. Actual enumeration then performs the
conversion at its real evaluation point. Diagnostic comparison probes also roll back
these changes. Deferred ToString enumeration requires proven SetPredValue provenance
and preserves EvalException instead of adding a Java-method wrapper.

A successful Cardinality conversion of a lazy filter is cached on that filter and shared
by aliases; membership then uses the converted enumeration, while the physical class
remains SetPredValue. Failed conversion does not populate the cache. Direct Print or
PrintT of a fresh filter over SUBSET in a difference follows the matching deep-normalize
order only when syntax, physical classes and the unconverted cache state are proved.
Held aliases without that proof retain the documented comparison limitation.

The trace evaluator sorts and deduplicates set elements with TLC's binary insertion order. It
returns the first comparison failure instead of passing a non-total comparator to Rust's sort,
which could panic on a mixed set. Integer-only sets use a stable integer sort with the same
first-duplicate retention: their comparisons cannot fail or normalize another value. This avoids
repeating binary insertion when random sampling normalizes large integer domains. The same stable
sort serves every set whose comparisons all succeed and normalize nothing but its own elements
(`sorts_without_effects`): elements all integers, all booleans, all strings TLC ranked at startup,
or all set enumerations whose elements, pooled, are such elements again, where only the top-level
sets may be held unnormalized (TLC compares, and so normalizes, each of two or more elements; a set
nested deeper is compared only where the sets before it are equal, so one held unnormalized keeps
binary insertion). Such a set normalizes each element and then sorts, and normalizing a set's
written elements only to find whether it fails skips the sort. Binary insertion compares n log n
times even on sorted input, which made a trace that prints 10^5 or more sets of integers 12 to 15
times slower than main and timed out `BugzillaBug279Test/InitStateBug`; the stable sort is linear
there. The map of unnormalized sets hashes addresses with a multiply rather than SipHash. Output is
unchanged (full suite byte-identical); `prints_sets_of_sets_in_a_trace_as_tlc` records TLC's trace
for unnormalized and nested sets of sets. The startup
fixtures record numeric-method errors and a lazy-set case that reached the panic on main, as well
as comparable sets and equivalent duplicates.

The trace evaluator follows TLC's `@@` override: both operands are evaluated before either
function conversion, both conversions precede the first/second argument checks, and added keys
are compared with the right key's equality method. Conversion and argument-formatting failures
are reported through `TLC.CombineFcn`, while failures evaluating an operand keep their own report
(`prove-it-cli/tests/startup_checks/function-merge-*`, recorded from TLC at d8fb231).

It still declines a new merge failure whose message depends on a function's discarded written
key order, or on formatting a mixed set inside a key-comparison error. It also declines new
conversion/type/comparison failures after the evaluator produced effects in a function body TLC
keeps lazy: those effects may belong after evaluation of the other operand. Argument diagnostics
use default formatting: concrete sets still normalize, while proven symbolic unions,
intersections and differences swallow expansion failures before formatting their parts. Other lazy
argument formats decline until the evaluator can follow that default expansion/fallback choice.
An unnormalized argument's outer comparison error is worded only when default formatting is proved
for every element: a nested formatting failure can mask it before TLC reports the comparison, as
in `{{{1, "s"}}, 1} @@ (1 :> 2)`. Otherwise that normalization remains an unworded decline.
Successful merges and failures evaluating an operand keep their existing behavior.

A failed normalization of an enumerated set can be replayed through a modeled Java method
wrapper when the physical enumeration class and every comparison operand's default formatting
are known. The replay also requires scalar assigned state slots at every enclosing value
evaluation entry, before assignment unwinding, and no lazy captures, speculative filter
execution, retained caught-error frames, pending fingerprint, unfollowed source or unprintable
state. A lazy value returned during replay also invalidates this proof. Function-construction
frames remain unsupported. Direct normalization consumers without
a modeled Java wrapper, including CHOOSE, UNION and Permutations, retain the existing decline:
their source-bearing fingerprint frames and wrapper behavior are not proved by this rule.

The trace evaluator follows TLC's typed integer Java methods too (`+`, `-`, `*`, `\div`, `%`,
`^`, `..` and unary negation): it evaluates their operands from left to right, then casts them
from right to left as the pinned JVM's MethodHandle spreader does. A failed cast names the Java
method of Naturals or Integers, its return type and the operand's concrete Java class
(`prove-it-cli/tests/startup_checks/integer-method-*`, recorded from TLC at d8fb231).

Integer addition, subtraction, multiplication, exponentiation and unary negation reproduce
TLC's coded overflow error with the evaluated operands. A failed startup definition still
requires proof that TLC reaches the same failure before replay can report it. Newly worded
overflows also remain unsupported after observed effects from a function TLC keeps lazy, or
while Print or PrintT forces a lazy value whose original exception source is not retained;
that source can change whether TLC reports the bare overflow or a Java-method wrapper.
Existing worded errors and successful values keep their previous behavior. CLI fixtures record
these arithmetic failures across startup, initial-state, successor and property evaluation,
including the pinned next-state exit code, error consumers and unused bodies.

A function's runtime class is retained separately from how it prints: an eager constructor is a
`FcnRcdValue`, and a constructor TLC keeps lazy remains a `FcnLambdaValue` even after its cached
contents are fingerprinted. Numeric type errors still decline where that provenance is lost:
functions reconstructed from the search or the existing transfer format, a lazy function's
EXCEPT whose cached conversion isn't followed, and an original function whose symmetry replay
only approximates that conversion. Sets likewise retain their physical class separately from
an enumeration of their contents: normalizing or caching a lazy set does not turn its original
Java object into a `SetEnumValue`. Set enumerations, intervals and lazy sets now retain that
provenance through held values, printing, copying and permutation. A numeric cast names the
class only where it is proved; generic scope, transfer and search reconstructions remain
unknown, as do class-dependent operations whose input's Java dispatch representation was lost.
Configuration assignments and operator-table results have a separate, proven origin:
`ModelConfig.parseValue` constructs their literal sets as `SetEnumValue`. That origin is cached
separately from generic values with equal mathematical contents. The transfer format and the
Bags methods' existing casts are unchanged.

The replay may evaluate the body of a finite function that TLC keeps lazy, including its effects.
After such effects, newly worded numeric cast errors and errors of a later operand reached only
because an earlier non-integer was evaluated decline. Errors the previous integer reader already
reached and successful evaluations keep their existing behavior. Distinguishing legitimate
startup normalization from effects whose placement differs takes retaining the lazy body and
following when TLC actually forces it.

An argument or a LET definition that is a constructor of one name over a set enumeration or an
interval, applied where its body may have effects (one of `EFFECTS`, through a definition, an
operator argument, a LET operator or a builtin passed as an operator) or where TLC holds its
domain unnormalized, or can't normalize it, is the FcnLambdaValue TLC's `LazyValue` keeps
(`OPCODE_fc` under `EvalControl.KeepLazy`): the replay keeps it as a lambda and evaluates its body
at each key it applies it to, with any number of arguments, asking the domain as TLC holds it for
the key (`FcnLambdaValue.apply`, `SetEnumValue.member`, `ValueVec.search` by `equals` where it isn't
normalized), so `F(f) == f[1] + f[1]` of `[i \in {1, 2} |-> Print(i, i)]` prints `1  1` twice and
nothing for 2, and `f[<<1>>]` of `[s \in {<<1>>, 20} |-> s]` holds. A constructor so written in
place is applied the same way, its outside-domain message printing the function as `toString`
builds it after the argument, as is a LET's name for one (`LET f == [n \in {1, 3} |-> n + 1] IN
AssertError(..., f[5])`, which main matched and the kept application had declined); so is one
that is the body of such a function where TLC applies it
under KeepLazy, as `f[1][1]` (`FcnLambdaValue.evalBody` with the application's control), and one an
EXCEPT updates there, whose `select` evaluates the body at the updated key and whose `takeExcept`
keeps it unbuilt. Another use of a kept one without effects in its body over a set TLC can
normalize builds it, as `toFcnRcd` does, normalizing the domain. A key outside the domain of a
kept one over a set enumeration TLC can't normalize, in an assumption, fails as that set's
`normalize` does before any key's body: the message's `toString` fails building it
(`FcnParams.size`), swallows that, and prints the domain unbuilt, normalizing it again
(`normalize_unsorted_failure_twice`), as `LET S == {1, "a"} f == [e \in S |-> e] IN f[mv] = 1`
with a model value `mv`, which main matched (`Attempted to compare string "a" with non-string:
1`). A second application of a constructor of one name over a domain TLC can't reduce, which it
keeps a FcnLambdaValue even where a use such as a print built it before (OPCODE_fc keeps one over
a set that isn't `Reducible`, as `SUBSET {1}`), with effects in its body but none in its domain,
evaluates the body at the key again, as `FcnLambdaValue.apply` does: `LET g == [i \in SUBSET {1}
|-> Print(i, 1)] IN PrintT(g) /\ g[{}] = 1` prints `{}  1` and `{1}  1` for the print and `{}  1`
again for the application, which main matched; the evaluator applies a lambda over the domain
evaluated again and keeps the function it built for other uses. These decline: any other use of a
kept one with effects in its body, with an EXCEPT, or over a set TLC can't normalize, which may or
may not build it (`toFcnRcd`), as `f = g`, `Print(f, TRUE)`, `DOMAIN f`, `<<f>>` or a membership ("a
function TLC keeps lazy in an argument, used but applied"); a key outside the domain of the kept
one, or of one nested in it, but the assumption's above; a second application of a constructor of
several bounds, of a tuple pattern, over a set enumeration or an interval, or reached through
`LET` or `IF`, with effects in its body, which the replay built at its first ("a function TLC keeps
lazy in an argument, with effects, applied again"); and a domain kept
unnormalized that the replay can't enumerate, as `{20, 10, "b"}` written in place ("a function TLC
keeps lazy over a set it can't normalize"). A constructor of several bounds with effects in its
body, written in place and applied once, still prints each key's effects as the replay builds it,
where TLC prints only the applied key's: a known wrong output.

A conjunct of an initial predicate or an action that names a definition TLC computed as it
started (`processConstantDefns`: no parameters, constant level, no effects, computed without
failing) is a guard the walk tests as that value, in the frame of the name alone, as
`getInitStates` and `getNextStates` look it up; the walk no longer descends into its body, whose
frame TLC's nested-expression trace never shows.

A definition TLC computes as it starts whose body prints, draws or sets a register, and whose value
is a function constructor that isn't recursive, over set enumerations and intervals
(`F == [n \in 1..2 |-> PrintT(n)]`, or the function definition `F[n \in 1..2] == PrintT(n)`),
the engine computes there too: TLC builds it at once (OPCODE_fc's `toFcnRcd`, as
`evalConstantDefn` evaluates with `EvalControl.Clear`), the body at each element of the normalized
domain in order, and its applications read the function it built. A constructor so built anywhere
the engine evaluates an expression as TLC does may print likewise, but where TLC evaluates the
function of an application, with `EvalControl.KeepLazy` (OPCODE_fa): that control reaches a
record's fields, an EXCEPT's parts, the set a CHOOSE picks from, an operator's body and a LET
definition or an argument at its first use, and OPCODE_fc keeps a constructor it meets lazy, so
`[a |-> [x \in 1..2 |-> PrintT(x)]].a[2]` prints only 2. The engine evaluates no print in a
function whose expression may meet such a constructor ("Print where TLC evaluates it otherwise"),
but where the function is the constructor itself, of one bound name, or the name of a LET's
definition that is such a constructor over a domain that evaluates no definition and reads no
register, which the LET names only as the function of applications: there TLC evaluates the
domain, then the argument, then the body only at the key (`FcnLambdaValue.apply`), once each
application, whether or not the LET keeps the function from its first use, and the engine builds
it lazy and applies it so (`[x \in {1, 2} |-> PrintT(x)][1]` prints 1, and `LET f == [x \in Nat
|-> P(x)] IN f[1] + f[1]` prints at each application). A key outside the domain, where TLC prints
the whole function as it fails (`Values.ppr(this.toString())`, which evaluates the body at every
element of the domain, printing before the error), declines ("a function TLC keeps lazy whose body
has effects, applied outside its domain"): the binary reported the failure without those prints
in the initial predicate, a step, an invariant, a property, a constraint and an action constraint
(`[i \in {1} |-> PrintT(i)][3]`; main declined these).
Where TLC computes the initial states from the application (`Tool.getInitStates`' OPCODE_fa, as
a conjunct, a disjunct, an arm or a body of the initial predicate, or of an operator or a LET it
applies there) it evaluates the function with `EvalControl.Init` rather than KeepLazy, building a
constructor over a set it reduces at once, its body at each key: the engine applies no such
constructor at the key only there, as before.
One over any other domain TLC keeps lazy, which the engine doesn't follow ("a value TLC computed
at startup with effects").

A recursive one (OPCODE_rfs) TLC keeps lazy too: `makeRecursive` binds its name, in its body, to
the very value `processConstantDefns` keeps, so every use shares it. TLC evaluates its body anew
at each application (`FcnLambdaValue.apply`), its own recursive calls too, until something
converts it (`toFcnRcd`, which only its own `equals` and `compareTo`, a fingerprint, and what
calls `toFcnRcd` on it, as `FcnRcdValue.equals` or a membership in a set of functions, do),
which evaluates the body at each element of the domain in order, applying itself lazily inside,
and caches the function it built (`fcnRcd`), which every later application reads without
evaluating anything (`F[n \in 1..2] == IF PrintT(n) /\ n = 1 THEN 1 ELSE F[n - 1]` with
`Test == F[2] = 1 /\ F[2] = 1` prints 2, 1, 2, 1; with `Test == F = F /\ F[2] = 1` it prints 1, 2,
1). The engine follows that where the body's only effects are prints, over one bound name of a
set enumeration or an interval without effects, and where the body is no function constructor and
meets none that prints, which TLC keeps lazy under the KeepLazy control `makeRecursive` sets: the
function it converted is kept in a slot of the machine every application reads first. Many uses
of it as a value don't convert it: `TupleValue.equals` and a set of tuples's membership select
each element anew without caching (`toTuple`: `<<1, 1>> = F`, `F \in Seq(Int)`, `F \in {<<1,
1>>}`), an EXCEPT selects the element `@` names and builds another lazy value (`takeExcept`), and
IF, CASE, a record, a set, CHOOSE or a quantifier pass the lazy value along to be applied anew. So
the engine converts it only where the expression is `F = e`, `F # e`, or `F \in [S -> T]` with
the global name F written as the left operand and the other written of constants or naming F
itself, which TLC converts after evaluating that operand, and stops at every other use of it as
a value ("a recursive function that prints, used as a value TLC may not convert"). TLC's
workers share that value, so the engine applies or converts such a function anew only while TLC
starts, on its one thread (the constant definitions and the assumptions); where the initial
predicate, an action, an invariant or a property would print by applying or converting one TLC
hasn't converted as it started, it stops ("a recursive function that prints, applied after TLC
starts"), and where something converted it there, they read what it built. The trace's evaluator
doesn't follow the conversion, so a report that evaluates such a function again declines ("a value
TLC computed at startup with effects"), as do several bounds, whose elements TLC converts with the
first varying fastest, a tuple pattern, a body that draws or sets a register, a print of the
function itself (which may fail to size its domain, "a set TLC may fail to print, at startup"), and
an application inside a Print's argument ("Print where TLC evaluates it otherwise").

A RECURSIVE operator TLC evaluates anew at each call, with no memo (`Tool.evalAppl`), binding
each argument to a `LazyValue` it evaluates where the body first reads the parameter. The engine
evaluates a call whose arguments neither print, draw, nor set or read a register as TLC does,
its body printing at each call (with no memo table where it may print or draw), and evaluates the
arguments before the body, which differs only where one fails, where it stops ("a failing
argument of a recursive operator that prints").

TLC checks each step against the action constraints as it finds it, after the constraints
(`Worker.addElement`, `Tool.isInActions`), with the state expanded as the current state and the
successor as the next: an action constraint may print where the native checker reports what the
search finds, without a liveness check, a VIEW or a symmetry, which would walk steps again.

TLC keeps a filter of a set it doesn't reduce lazy (OPCODE_sso, a `SetPredValue`) and evaluates
its predicate as it enumerates it, at each use. Where the filter of a product or of a set of
records of set enumerations and intervals is the left operand of `=` or `#` whose right operand
has no effect, and the filtered set has none, TLC evaluates the right operand and then the
predicate once at each element (`SetPredValue.equals`, `convertAndCache`), each factor's or
field's elements in their normalized order with the last varying fastest
(`SetOfTuplesValue.Enumerator`, `SetOfRcdsValue.Enumerator`): the engine compares it so, so its
predicate may print. Any other use of such a filter whose predicate prints declines as before.

A definition kept for the warning an EXCEPT
may give (`STARTUP_WARNING_ONLY`) that TLC computed as it started without one has no effect: the
evaluator of failures computes it again where a failure reads it, as main did, so `E == [<<0, 1>>
EXCEPT ![1] = 2]` with `Inv == E[3] = 0`, or `D == [[a |-> 1] EXCEPT !.a = 2]` beside a division
by zero, words TLC's failure (`except-*` fixtures), and declines only where that computation
warns, which TLC did as it started and doesn't again ("a value TLC computed at startup with a
warning").

The liveness level of an application of an operator that applies an operator argument counts
that argument's level, as SANY's does (`Specs.getLevel`, `getLevelParams`), so `<>(Apply(G)...)`
with `G(k) == x + k` is a state predicate rather than a constant TLC evaluates as it starts. It
counts it only where the body applies the argument at weight 1: `OpApplNode.levelCheck` adds an
operand's level parameters only for a weight-1 operand (`BuiltInOperators`), and ENABLED, ',
UNCHANGED, `[A]_v`, `<<A>>_v`, WF, SF, [], <> and the temporal quantifiers take theirs with weight
0. So `Over(F(_)) == ENABLED F(2)` applied to an action `Op` is a state predicate, and
`PROPERTY Prop` with `Prop == [](Over(Op))` is an invariant TLC reports violated by the initial
state, not a temporal property.

An error in a function's bounds can still decline under the failed-startup confirmation guard,
which does not yet distinguish the bounds from a body TLC may keep lazy. A CHOOSE over an
unresolved lazy UNION can also reach that guard; a concrete class alone does not prove that
TLC chooses the same element.

Two adversarial forms retain an existing wrong error wrapper: for
`S == {k \in SUBSET {1} : 1 \div 0 = 0}`, `ASSUME Print(0, S) + 1` and a LET alias of that
Print report the Java Print method around the division error, where pinned TLC reports the
division error directly.

A missing argument to a function constructed eagerly from proven physical set-enumeration
or interval domains reports the function-record diagnostic. The construction records this
proof on the function itself; it is independent of presentation normalization and of a lazy
function's conversion cache. Unproved domains and transferred function values keep their
previous behavior; this proof admits no new diagnostics for them. Existing lazy-function
diagnostics are unchanged.

The trace evaluator follows `Sequences.Append` and `Sequences.Concat` diagnostics too: both
operands evaluate from left to right before conversion; a string on the left of concatenation
requires a string on the right, and other operands convert to sequences from left to right.
An invalid operand prints with TLC's default formatting, whose normalization failures are
reported as failures of the Java method. Default formats not yet proved by the shared formatter
guard still decline (`sequence-*` startup fixtures,
recorded from TLC at d8fb231).

Append follows Sequences.Append/OpValue.eval: both operand values are constructed before the
first is converted to a tuple. For proved packaged Nat, Int, STRING and Seq values in the first
position, run their construction parts and the second operand's parts, then report the existing
sequence type failure. Other first operands are evaluated and checked by their actual store kind;
a tuple retains the prior appended-element evaluation. A generic Lazy reference is not a set
certificate: IF/CASE references can contain tuples or eager functions.

The new construction path, and the evaluator proof below, retain the previous Append binary
path/guards when any reachable builtin has EXTERNAL_CLASS provenance, or a named-set builtin
has any nonzero flags (including TABLE, STATE_LEVEL, DECLINED, OPAQUE_TABLE and future flags).
EXTERNAL_CLASS=256 is negative provenance from explicit ModelOrigin facts: only Default Java
profile and definite absence of every relevant standard, bundled, user and index class permit
this new admission. Present entries (including directories/FIFOs), Unknown I/O, legacy sources
without origin facts and opaque launch profiles retain the old path. A model-wide negative pass
covers definitions whose owning builtin is not lowered. Presence checks do not open class bytes;
legacy early-error probing is error-only and cannot issue a successful model or positive proof.
Any/Json.ToJson's old
DECLINED behavior is unchanged. This is a capability fallback to the prior implementation,
not an environment-wide decline: unused/dead-branch class controls keep their old matches.

Where first-argument conversion fails, Append never normalizes its discarded second value.
An immediate set enumeration of only number/string literals that is held Unsorted therefore
restores only the is_unsorted flag from before that operand; earlier uncertainty is preserved.
Arbitrary expressions, nested/consumed sets, effects, definitions and successful conversions
keep the earlier guards. The same packaged-construction capability gate applies here.

Jar-backed startup-append-construction-* and startup-append-proof-* fixtures cover all five
consumer contexts, inline/named effects, eager/empty/lazy functions, IF/CASE/aliases/state-held
function classes and the discarded/consumed literal-set boundary. The actual Append slice
has 225/227 pinned-Jar matches, with two outer random startup definitions still declining:
random_02367#assume and random_08197#assume; their unsupported outer phase is not skipped.

The composed real-class/index grid preserves all old matches; known legacy wrong results remain
explicit follow-up work and are never recorded as expected outputs. Target-specific index metadata
cannot replace the conservative capability guard without equivalent definition-operand coverage.

A failed startup definition evaluated again, where a function TLC keeps lazy over a set its
module overrides (`[x \in Nat |-> x]`) fails to convert in `FcnLambdaValue.toFcnRcd` with
"Attempted to compute the number of elements in the overridden value Nat.", answers where TLC
takes `toFcnRcd` itself: `@@` (`CombineFcn` converts the first argument, then the second, before
testing either), the Bags methods, and a field selection (`OPCODE_rs`). A comparison or an
equality with such a function follows TLC's receiver, as the paragraph on startup failures above
says (`lambda_as_operand`). A membership in a set of functions or records still declines ("built a
function over a set TLC doesn't enumerate, where TLC may not"): a set of functions with a source
fails in its `member` as a fingerprint failure the evaluator doesn't always place
(`<<[x \in Nat |-> x]>> \in Seq([{1} -> {1}])` under init).

A failed startup assumption evaluated again whose failure is an enumeration's where the
evaluation holds a power set TLC keeps lazy (`SUBSET {1, 2} \cup 1`) answers where the evaluator
walked no power set's elements other than to print them: TLC prints a `SubsetValue` through
`toSetEnum` normalized, whatever order `SubsetValue.elements` walks it in, so its text is the
evaluator's. Where the evaluation walked one otherwise (a filter, a map, a quantifier, a CHOOSE
over `SUBSET {1, 2}`), what it meets first may differ, and it still declines; the same failure
outside an assumption still declines, since a lazy set TLC gave a source may fail in its method
as a state TLC fails to fingerprint.

A failed startup assumption evaluated again that built a set TLC can't normalize
(`{1, "a"}`), which TLC holds as written until it compares, counts, fingerprints or prints it,
answers where the evaluator printed no such set on the way (`print::unsorted_prints`, which counts
each text the evaluator writes of one, where `SetEnumValue.toString` fails comparing), whatever the
failure: each other place TLC normalizes the set (`compareTo`, `equals`, `size`, its Enumerator,
`randomElement`, Print's and TLCEval's `deepNormalize`) the evaluator fails in as TLC does, so the
failure it reaches is TLC's, as a Java integer method's cast (`3 \div {1, "a"}`), a non-function
applied, `<<{1, "a"} \cup {2}, Head(<<>>)>>` or `CHOOSE` that finds nothing beside such a set
(probed against the jar over some 1,000 shapes of 70 operators on `{1, "a"}`, `{<<1>>, [a |-> 1]}`
and `{{1}, 1}`), but for the Java methods that word a wrong argument with its value, which "Known
wrong outputs" lists. A failure whose message prints the set still declines: `Len({1, "a"})` and
`2147483647 < {1, "a"}` print it, which fails in TLC. Outside an assumption the same failure
still declines.

`TLCEval` deep-normalizes the value it returns (`TLCEval.tlcEval`'s `deepNormalize`) for an
argument of constant level in an empty `Context` (`tlcEvalConst`), which the evaluator now
follows: a value holding a set enumeration TLC can't normalize fails comparing as the Java method's
failure (`TLCEval({1, "a"}) + 1`), where `eval::deep_normalize` knows the order TLC walks the value
in, and otherwise declines ("TLCEval of a value holding a set TLC can't normalize, in an order the
evaluator doesn't know"; in TLC 1.7.4, whose Java override the evaluator doesn't follow, always).
Before, the evaluator returned the value and failed later, or not at all, where TLC failed in
TLCEval, which answered wrong in an assumption. Under a bound name, an operator's parameter, a
LET's zero-arity definition, a function definition or `@` of an EXCEPT, in TLCEval's own scope or a
caller's (`getOpContext` conses onto the caller's `Context`), TLC converts the value alone and
fails later where it is used (`\E y \in {1} : TLCEval({y, "a"}) = {}` fails in
`SetEnumValue.equals`), which the evaluator follows (`eval::Held`). Where the evaluator doesn't
know whether TLC's `Context` is empty, beside a LET operator with parameters or an operator
argument, in a copy an INSTANCE with substitutions makes (its `SubstInNode` conses them, so
`INSTANCE Inner WITH K <- 1` with `Mixed == 1 \in TLCEval({1, "a"})` finds no error in TLC, and
an INSTANCE without WITH substitutes a declared constant all the same), under a LET a walk of the initial predicate or the next-state relation bound
(`getInitStates`, `getNextStates` and `getActions` don't cons it), or for an argument that may
read the state, such a value declines ("TLCEval of a value holding a set TLC can't normalize,
where TLC may or may not normalize it").

`EvaluatingValue.eval`, which runs TLCEval, catches whatever its Java method throws, a
FingerprintException too, and fails again with `Assert.fail` (2154): where TLCEval's argument
fails in a method of a value with a source (`TLCEval({1, "a"} = {2})`, `TLCEval(<<{1, "a"}
\subseteq {1}>>)`, `TLCEval({{1}, {"a"}} = {})`, `TLCEval(<<<<1>>[2]>>)`, in a tuple, a record, a
set, under `Len` or a quantifier), TLC reports the nested expressions (2103) of the call stack the
FingerprintException froze (`CallStack.freeze(FingerprintException)`), its frames followed by the
sources of its values, where the binary printed "TLC was unable to fingerprint." with the same
frames (main declined in the initial predicate, an invariant and a property, and printed the same
elsewhere). The evaluator now drops the FingerprintException at TLCEval (`catch_fingerprint`),
keeping its sources as frames, and words the failure as TLC does in every context but the
next-state relation, where a set the argument holds unnormalized declines ("a set TLC leaves
unnormalized"; it printed the FingerprintException there, as main did or declined).

Not under a CHOOSE, a quantifier, a set filter or a set map whose set is a set enumeration TLC
fails to sort (`TLCEval(\A z \in {{1}, {"a"}} : TRUE)`,
`TLCEval(\E z \in S : TRUE)` of `S == {1, "a"}`, `TLCEval(CHOOSE z \in {1, "a"} \cup {} :
TRUE)`): TLC's enumeration of the set (`SetEnumValue.elements`, `normalize`) throws the failure on
as a FingerprintException with the set's source, a constant definition's set too, and, for a set
of sets, the source of the element whose `compareTo` failed, which the replay doesn't follow. The
binary printed the stack without those last frames in the initial predicate, a step, an invariant
and a property (main declined, or was wrong alike for a constant definition's set); it now declines
there ("the enumeration of a bound set enumeration TLC fails to sort, with its source",
`UNSORTED_BOUND_SOURCED`), but for a set of scalars the replay built with its source, whose
`normalize` throws the failure on with that source alone (`CHOOSE x \in {1, "a"} : TRUE`, `\E x \in
{1, "a"} : x = 1`, `TLCEval(CHOOSE z \in {1, "a"} : TRUE)`), which it words as TLC does. An assumption, whose failure TLC reports without
frames, still matches.

A TLCEval whose argument fails in another TLCEval that caught a FingerprintException
(`TLCEval(TLCEval(<<1>>[2]))`, `TLCEval(TLCEval({1, "a"} = {2}))`, `TLCEval(TLCEval({1} \cup 2))`,
`TLCEval(Len(<<TLCEval(<<1>>[2])>>))`, `LET F == TLCEval({1, "a"} = {2}) IN TLCEval(F)`) TLC, in
the initial predicate, a step, an invariant or a property, reports with the nested 2154 and then
never prints the nested expressions nor exits; the binary printed them and exited. It now declines
("a TLCEval failing in another TLCEval's caught FingerprintException, which TLC hangs reporting").
A TLCEvalDefinition inside the TLCEval catches and fails again alike, and TLC hangs alike
(`TLCEval(TLCEvalDefinition("D"))` of `D == <<1>>[2]` or `D == {1, "a"} = {2}`); the binary
printed the nested expressions and exited, and now declines it as well (main declined these). A
TLCEval of a set TLC keeps lazy, whose operand may have an effect (as TLCEvalDefinition's), TLC
enumerates within the Java method, failing as it (`TLCEval(TLCEvalDefinition("D"))` of `D == {1}
\cup 2` reports the 2154 of `TLCEval.tlcEval`), where the evaluator kept it lazy and reported the
enumeration's failure without that wrapper: it declines ("TLCEval of a set TLC keeps lazy whose
operand may have an effect").
One whose inner failure has no source (`TLCEval(TLCEval(1 \div 0))`, `TLCEval(TLCEval(Head(<<>>)))`,
`TLCEval(TLCEval(CHOOSE z \in {} : TRUE))`, `TLCEval(TLCEval([a |-> 1].b))`) TLC reports as any
other, and the binary matches it; an assumption matches either way.

In an assumption, a TLCEval applied as a function (`TLCEval([z \in {1, "a"} |-> z])[1]`) keeps
its argument lazy (`EvalControl.KeepLazy`), where the evaluator declined a function constructor
over a set enumeration TLC can't sort ("a function TLC keeps lazy over a set enumeration it can't
sort", "a function over a set TLC fails to sort"), which main matched. TLCEval's `convert` builds a
constructor written as its argument (`FcnLambdaValue.toFcnRcd`), counting its domains in order
(`FcnParams.size`), so the evaluator now counts them as it does (`counted_domains_failure`), and
evaluates an argument of constant level in an empty context (`tlcEvalConst`, without the
application's control) again keeping no function lazy (`TLCEval(<<[z \in {1, "a"} |-> z]>>)[1][1]`).
Such a constructor inside the argument over a domain that fails comparing a function or a
record (`TLCEval(<<[z \in {<<1>>, [a |-> 1]} |-> z]>>)[1][<<1>>]`, the
`tlceval-constructor-over-record-and-tuple` startup fixture) declined too, where main matches:
evaluated again so, the evaluator builds each constructor nothing keeps lazy and fails as its
`FcnParams.size` does, on the first domain that is a set enumeration TLC can't sort, where every
domain is `Reducible` (`builds_unsorted_domains`). 1,000 probes, 40 shapes over 5 such domains
(as `{[a |-> 1], <<1>>}` and `{[x \in {1} |-> 1], [a |-> 1]}`) in every context, matched the jar
or declined, and 46 of them answer now. `FcnParams.size` counts every domain before `toFcnRcd`
enumerates any, so the evaluator counts them so wherever TLC builds a constructor of several
bounds (`count_domains`): a set enumeration TLC can't sort past an empty domain fails, where the
evaluator, enumerating, stopped at the empty one and answered (`[z \in {}, w \in {1, "a"} |-> 1]
= <<>>` held, a false success, and `TLCEval(<<[z \in 1..0, w \in {TRUE, 1} |-> 1]>>) = <<>>` was
false, where TLC fails comparing; wrong on the earlier binary, declined on main); and a count past
2^31 - 1 elements fails as its message prints the domains (`FcnParams.toString`), on the first set
enumeration TLC can't sort (`TLCEval(<<[z \in 1..70000, w \in 1..70000, v \in {<<1>>, [a |->
1]} |-> 1]>>)`, which main matched). Outside an assumption TLC traces such a failure past an empty
domain to the set's own source (`SetEnumValue.size`), which the replay doesn't follow ("a
function's domain TLC counts, failing, past one its enumeration stops at, where a call stack
traces it"), and a function TLC keeps lazy (a domain not `Reducible`, or under KeepLazy) whose
domain past one that may be empty holds a set TLC can't sort declines ("a function TLC keeps lazy
whose domain past an empty one it can't sort"; `[z \in {}, w \in SUBSET {1, "a"} |-> 1] = <<>>`
answered falsely before), as both fail as a use builds the function. 255 probes of 51 such shapes
in every context, against the jar and main at one and four workers, matched or declined.

Not only TLCEval's argument: anywhere in an assumption, whose failure TLC reports without frames
and whose values have no source, a constructor nothing keeps lazy over set enumerations and
intervals (`Reducible`) is one `Tool`'s OPCODE_fc builds (`toFcnRcd`), whose `FcnParams.size`
fails on the first set enumeration TLC can't sort comparing a function or a record, so the
evaluator counts the domains there too (`counted_unsorted_failure`): `<<DOMAIN [x \in {<<1>>, [a
|-> 1]} |-> x], Head(<<>>)>>` fails comparing the record with the tuple, which main matched. One
an application keeps lazy (`[x \in D |-> x][<<1>>]`, an EXCEPT of it) and one outside an
assumption still decline ("a function over a set TLC fails to sort").

Still declined, where main matches: such a constructor under a function TLC keeps lazy
(`TLCEval(<<[x \in Nat |-> [z \in D |-> z]]>>)[1][1]`, whose failure TLC reports without TLCEval's
wrapper, as the application builds it), in an argument of a level above constant or with a context
(`\A x \in {1} : TLCEval(<<[z \in D |-> x]>>) = 1`, which TLC evaluates without `tlcEvalConst`),
over a domain TLC doesn't reduce (`SUBSET D`, `{1} \X D`, alone or as the body of a function TLC
builds), and a LET's name for one TLC keeps lazy as an application evaluates it and that the
argument then holds (`TLCEval(LET f == [z \in D |-> z] IN <<f[<<1>>], f>>)[1] = <<1>>`). TLC
holds each such function lazy (`FcnLambdaValue`) and fails on D only where `tlcEvalConst`'s
`deepNormalize` reaches the function's domains, after the whole argument evaluated, and only if
the function is still in the value. Main sorts every set enumeration as it builds it, which
matches TLC only by chance in these shapes; in their neighbours main is wrong, with D `{<<1>>, [a
|-> 1]}`: `TLCEval(<<[z \in SUBSET {1}, w \in D |-> 1], 1 \div 0>>)`, the same with
`[y \in {1} |-> [z \in SUBSET {1}, w \in D |-> 1]]` and `TLCEval(LET f == [z \in D |-> z] IN
<<f[<<1>>], f, 1 \div 0>>)` fail on TLC as `\div`'s second argument is 0, where main fails
comparing the record; `TLCEval(<<[z \in SUBSET {1}, w \in D |-> 1][{1}, <<1>>]>>) = <<1>>` and
`TLCEval(LET f == [z \in D |-> z] IN <<f[<<1>>], 1>>)[1] = <<1>>` hold on TLC, which applies the
function searching the domain as written, where main fails comparing the record (the latter now
answers here); and `TLCEval(<<[z \in {<<1>>, [a |-> 1]} |-> z][<<1>>]>>) = <<<<1>>>>` holds on
TLC where main fails. These are declines to win back by following the lazy function into
`deepNormalize`.

A failed startup definition evaluated again in an assumption whose failure is an expected value
(an integer, a boolean) or a sequence method's argument beside a union, intersection or difference
TLC keeps lazy (`SetCupValue`, `SetCapValue`, `SetDiffValue`) no longer declines ("a startup
definition that failed where TLC may fail otherwise"): no value has a source there, and the
evaluator words such a set as its `toString` does, expanded where `toSetEnum` succeeds and as
written otherwise; 440 probes of 22 operators (`<`, `+`, IF, CASE, `~`, Head, Len, SubSeq,
SelectSeq, SortSeq, `\o`, a filter's predicate and others) over 20 such sets matched the jar or
declined. Outside an assumption it still declines.

Two more such failures of a failed startup definition evaluated again in an assumption no longer
decline: one that enumerates something beside a power set the evaluation walked, since TLC walks
a `SubsetValue` by size and then in its base's order (`SubsetValue.elementsNormalized`), which is
the evaluator's sorted order (probes whose failure depends on the element met first, as
`\A s \in SUBSET {1, 2, 3} : \A x \in (IF s = {3} \/ s = {1, 2} THEN s \cup Nat ELSE {}) : TRUE`,
under quantifiers, CHOOSE, filters, maps and PrintT, matched); and a sequence operator's argument
that isn't a sequence beside a function TLC keeps lazy, which the evaluator converts as `toTuple`
does. Outside an assumption both still decline.

The trace evaluator streams a lazy intersection, union, difference, UNION and a filter it
filtered ahead in the order TLC's Enumerators give their elements (`sets::stream`):
`SetCupValue.Enumerator` the first operand's and then the second's, `SetCapValue`'s and
`SetDiffValue`'s the elements of the set they enumerate that the other holds or lacks, as they
test them, and `UnionValue`'s the elements of each of its sets in the normalized order of the set
of them, each set streamed so in turn. What a consumer collects of them it normalizes in that
order (`toSetEnum`, `ValueVec.sort`), which decides which two elements TLC compares first, as
`Cardinality({1} \cup SUBSET {1})` compares `{}` with `1`; a membership test or a filter's
predicate meets the elements in that order too, before any sorting, as
`CHOOSE b \in ((lambda :> 2) \cap UNION {{2, 1, 3}, SUBSET {1}}) : TRUE` asks the function of `{}`
first. Each Enumerator's start is followed as TLC makes it, before any element: a set enumeration
normalizes itself, a union of operands checks that both are enumerable and starts both, a set of
functions, records or tuples asks whether it is empty (`Value.isEmpty`, which fails on a part
that isn't a set, in order up to an empty one) and checks and starts each part, and a UNION starts
its first set. CHOOSE normalizes its set first (`OPCODE_bc`'s `normalize`), which sorts the set
enumerations an intersection, a difference, a filter, a power set or a set of functions, records
or tuples is made of. An equality whose left operand is a lazy set converts that set before the
right operand (`convertAndCache`), but where both are of a class that compares their parts. A lazy set
converts itself (`convertAndCache`) where it is compared, equated or counted, which deep-normalizes
the set enumeration it makes, failing on a set TLC holds unnormalized anywhere in it. A power set
counts its base before it enumerates it (`SubsetValue.elementsNormalized`), which a base TLC can't
count fails. An Enumerator's message names its operands with their `toString`, which fails first
where printing one fails, as a set enumeration TLC can't sort. An interval too large to build is
walked, as `IntervalValue.Enumerator` walks it, where TLC streams it (an intersection's, a union's,
a difference's or a filter's Enumerator, `isSubsetEq`, OPCODE_sso, `IntervalValue.cap` and
`diff`), and what TLC collects of it is bounded as `ValueVec.addElement` bounds it ("Attempted to
construct a set with too many elements (>1000000)."), as `IntervalValue.cup` adding the interval's
own elements is, and as `SetEnumValue.cup` and `IntervalValue.cup` adding the other set's elements
they lack are (`Cardinality((1..1000000) \cup {0})`, `Cardinality({0} \cup (1..1000001))`). The
engine stops where a union, an intersection or a difference TLC may reduce collects more than
1,000,000 elements, an intersection or a difference with Nat, Int or STRING among them (`a set TLC
collects past its bound on a set's elements`), and the evaluator of failures evaluates the model
again, which words TLC's failure or declines; it is counted where TLC counts it (`IntervalValue.size` in `toSetEnum`, a
comparison, an equality or a function TLC builds over it), which fails past 2^31 - 1 elements.
A walk of more than four million elements, which TLC may take for billions, declines, as does one
where the search stopped at a value TLC can't enumerate or count. A function whose lazy domain
fails to enumerate is kept lazy, as TLC never enumerates it to build it. With
these, a failed startup definition evaluated again in an assumption no longer declines for a lazy
union or a failed sort of what such a set enumerates ("a startup definition that failed where
TLC may fail otherwise"): 75 of the 144 such runs of the upstream suite and some 4,000 random
expressions in the suite's style matched the jar or declined. Outside an assumption both still
decline.

An assumption the engine fails on comparing two values the store can't compare, which TLC may
never compare where it holds a set as built and searches it element by element or streams a lazy
set, is left to the trace evaluator, as one at a limit of the engine's is: TLC computes
`1 \in {IF x = 1 THEN 1 ELSE "a" : x \in 1..2}` and `"a" \in UNION {1..2, {"a"}}` (which asks the
smaller set first), and fails `2 \in {1, "a"}` on `"a"`'s `equals`. An assumption the evaluator
evaluates again after the engine failed on it, and finds false, is reported false as TLC reports
it (`Assumption ... is false.`). 1,500 random boolean assumptions in the suite's style matched the
jar or declined wherever main matched or declined; 5 where main is wrong stay wrong.

The evaluator models where `toString` throws, class by class (`check_to_string`): a lazy set that
expands itself to print swallows a failure of its expansion only where its caller asks it to
(`Value.toString` does, `toStringUnchecked` doesn't) and prints its operation instead, but a
`UnionValue`, which catches nothing, and a `SubsetValue` of a base under 7 elements, which
expands outside its catch, throw; a function TLC keeps lazy prints each domain with
`Value.toString`. So `PrintT([b \in UNION {1} |-> 0])` fails in PrintT's Java method enumerating
the UNION, where the evaluator printed `UNION({1})`, a text TLC prints only under `-terse`. A
report whose message prints a union or a small power set that fails to expand so declines ("a
message that prints a lazy set TLC fails to expand"), as does a message of a membership in a lazy
set whose values TLC may fail to print where the evaluator doesn't hold their classes ("a
membership's message whose values TLC may fail to print"), and a set whose expansion fails to
print after TLC began to write it ("a lazy set whose expansion fails to print, which TLC
swallows"). A function or filter TLC keeps lazy prints its body or predicate as SANY's
`toString` of the node, which is a numeral's or a decimal's image as written: `[x \in Nat |-> 2]`
prints `[x \in Nat |-> <expression 2>]`, and `[x \in Nat |-> 007]` and `[x \in Nat |-> \b101]`
print `<expression 007>` and `<expression \b101>` (the front end keeps the image of a numeral
written otherwise than its value in decimal). A numeral or decimal whose node doesn't span its
image declines where such a value is built ("a lazy value's expression written as a numeral the
evaluator can't word"). A function over a lazy set
that holds a set enumeration TLC can't sort declines ("a function TLC keeps lazy over a set that
holds one TLC can't sort"): TLC keeps it lazy and normalizes that set as it prints it, which the
function the evaluator builds no longer holds. `IsFiniteSet` of a function TLC keeps lazy fails
as `FcnLambdaValue.isFinite` does, and of one it built is TRUE, as `[x \in {} |-> 1]`; one the
evaluator doesn't know TLC built declines. A function of a set of functions (`SetOfFcnsValue`'s
Enumerators) is held normalized, so applying it to a key it can't compare fails in the first key's
`equals`, as `(CHOOSE f \in [{1, 2} -> {2}] : TRUE)[FALSE]` fails comparing 1. The quantifier bound
`\A x \in S` no longer prints S where TLC doesn't refuse it, which normalized the sets S held.

An unbounded `\E` or `\A` in an assumption fails as `Tool.eval`'s OPCODE_ue and OPCODE_uf do ("TLC
attempted to evaluate an unbounded \E.", the form, and where it is), as an unbounded CHOOSE
already did; it declined before ("evaluating a an unbounded quantifier"). SANY keeps an assumption
constant-level, so no `\EE` or `\AA` reaches it. Elsewhere, where TLC reports it otherwise, it still
declines.

An equality of a function over integers (a `FcnRcdValue` or a `TupleValue`) with a record, or with
a function over strings, either way round, no longer declines in the trace evaluator ("record
compared with a function"): TLC takes the other as a function (`toFcnRcd`), compares the sizes,
then the keys, where an integer key equated with a string fails in the key's `equals`
(`(1 :> 0) = ("a" :> 0)`: "Attempted to check equality of integer 1 with non-integer"), or, against
a function over an interval, in `FcnRcdValue.equals` ("Attempted to compare an integer with
non-integer"). A record on the left still fails as `RecordValue.equals` does, and a domain of
mixed keys still declines. The engine's own comparison (`tla-values`) still declines it.

PrintT of `Seq(S)` prints `Seq(` and S's text (`Sequences.toString`), which a set enumeration
TLC can't normalize fails to write: `PrintT(Seq({1, "a"}))` fails comparing within PrintT's Java
method, where the evaluator printed `Seq({1, "a"})` (`check_unchecked` now follows the base).

Print and PrintT normalize a copy of each value deeply before they print it
(`Value.deepNormalize`), which the evaluator follows three times over: `deep_normalize_print`
(above) sorts the sets TLC holds unnormalized, `eval::deep_normalize` places the failure of a set
TLC can't normalize, and `value::print_normalize` (below, where every printed set's Java class is
known) follows the walk whole. All three walk the values before the print settles them; a failure
`print_normalize` or `deep_normalize` claims answers where the other claims the same failure or
nothing, and the print declines where one claims a failure and the other to have followed every
value without one ("a print whose deep normalization the walks disagree on"): `SetCupValue` its first set and then its second, the elements of a set
enumeration and the values of a tuple before the set itself, so `PrintT(SetToBag({1}) \cup {1, "a"})`
fails comparing as the walk first reaches a set TLC can't normalize, which the evaluator now does
(`eval::deep_normalize`). Where the order TLC walks one in is unknown to the evaluator (a lambda,
a function's domain, a record or function holding more than one such set, a lazy set of a
physical class evaluation lost), the walk claims nothing and the print keeps its previous
behaviour; a failure `deep_normalize_print` then finds past that point answers only where printing
the values fails with the same message, and declines otherwise ("a printed value whose deep
normalization may fail elsewhere"), and its decline for a walk it doesn't follow gives way to the
print's own failure where the values hold a set TLC can't normalize. `TLC.Print` normalizes its first argument before its second, so once the walk claims
nothing for the first it claims nothing for the second either: TLC may fail inside the first
(`Print([a |-> {1, "a"}, b |-> {2, "b"}], {3, "c"})` fails comparing `"a"` with `1`).

A failed startup definition evaluated again whose failure is in a function constructor's domain
(`[x \in 0..[a |-> 1] |-> x]`, `DOMAIN [b \in CHOOSE f \in {} : TRUE |-> 1]`) answers: TLC
evaluates every domain as it meets the constructor (`Tool.evalAppl`'s `OPCODE_fc`), lazy or not,
before it builds a `FcnLambdaValue`. A failure in the body of a constructor of a single name over
a set enumeration or an interval TLC doesn't keep lazy (`is_built`, with the set's Java class
known) answers in an assumption: `Tool`'s OPCODE_fc builds that function as it meets it
(`toFcnRcd`), evaluating the body at each element of the normalized domain in order, as the
evaluator does (`PrintT([x \in {1, 2} |-> Head(<<>>)])`, `[x \in 1..3 |-> IF x = 2 THEN Head(<<>>)
ELSE x]`). A failure in the body of any other constructor (`unfollowed_constructions`: several
bounds, a tuple pattern, a domain TLC holds lazy, as a SUBSET or a filter of a set TLC doesn't
reduce, or one TLC keeps lazy as the function of an application), and any such failure outside
an assumption, still declines ("a startup definition that failed where TLC may fail otherwise"),
since TLC may evaluate that body later, in another order, or not at all, and its
`FcnLambdaValue.toString` prints the function unbuilt where building it fails.

A failed startup definition evaluated again whose failure is a sequence method's argument that
isn't a sequence (`Head({1, 2} \X {3})`, `Len(SUBSET {1, 2})`, `Tail(Seq({1}))`) answers beside a
set TLC keeps lazy: the method takes `toTuple`, which no lazy set converts, and prints the set
(`Values.ppr(s.toString())`) as Print does. Beside a function TLC keeps lazy (`FcnLambdaValue`,
which `toTuple` converts) it still declines.

A failed startup assumption evaluated again whose failure is `UnionValue.Enumerator`'s first
element that isn't `Enumerable` ("Attempted to enumerate UNION(s), but some element of s is
nonenumerable.", `PrintT(UNION 1..3)`) answers where the evaluation held one lazy union, of a set
none of whose elements TLC enumerates, so the first element TLC's walk gives fails whatever order
it walks in. A union of a set mixing sets and non-sets (`UNION {{1}, 1}`), a later element that
fails ("when enumerating: ...UnionValue$Enumerator@..."), and other failures beside a lazy union
still decline, as does the same failure outside an assumption.

A failed startup definition evaluated again whose failure is Print's or PrintT's deep
normalization (`PrintT(FALSE \X {1, "a"})`) answers beside a Cartesian product or a power set:
`SetOfTuplesValue.deepNormalize` normalizes each factor in order and `SubsetValue.deepNormalize`
its base, which `eval::deep_normalize` walks. Other comparisons that fail beside one still
decline.

A failure whose TLC message prints a set enumeration TLC can't normalize (`Len({1, "a"})`, `2 < {1,
"a"}`, `{1, "a"} \in Int`, `<<1, 2>>[{1, "a"}]`, `{1, "a"}.a`, `Int = {1, "a"}`, `BagCardinality({1,
"a"})`) fails instead where `SetEnumValue.toString` normalizes that set, comparing
(`value::print_failure`), as any normalization of the set does: within the Java method's failure
where a method prints it (Sequences' Len, Head, Tail, SubSeq and SelectSeq, TLC's SortSeq, Bags'
BagCardinality and BagToSet, and LT, LE, GT and GEQ of Integers, whose GT returns a `BoolValue`, or
of Naturals). Only a set printed at the top of the message, whose normalization the evaluator
follows, answers so (other Java methods that print an argument holding such a set are known wrong
outputs, listed there); a comparison whose module the IR's builtins don't tell (no arithmetic
builtin or `>=` beside it) keeps the evaluator's earlier failure. Where TLC reports such a failure
as a FingerprintException, in a state or a step, the set's `getNewHead` adds its source, which the
evaluator can't place, and the failure declines as a named normalization does ("a set TLC fails to
normalize as it words a failure, in a fingerprint stack"), as `<<1, 2>>[{1, "a"}]` in Next.

A failed startup assumption evaluated again whose failure is `UserValue.compareTo`'s ("Attempted to
compare overridden value Int with non-overridden value:", `Int = {1, 2} \X {3}`) answers beside a
Cartesian product or a power set, whose text the evaluator prints as TLC's `toString` does. One
beside a union TLC keeps lazy answers where every such union the evaluation built is of a set
enumeration of set enumerations and intervals that hold no set TLC can't normalize
(`CHOOSE x \in UNION {1..3, {}} : FALSE`), which `UnionValue` enumerates, prints and tests
membership in through its sets in order, as the evaluator does; a failure of a membership, a
comparison, an enumeration or a union beside one, a union of anything else, and the same failures
outside an assumption still decline.

A failed startup definition evaluated again whose failure is a tuple pattern that doesn't match
in a set map or a quantifier (`{a : <<a, b>> \in 1..3}`, "Argument mismatch in operator
application.%1") answers: `ContextEnumerator.nextElement` fails as the walk of the set, in
normalized order, reaches an element that isn't a `TupleValue` of the pattern's length, as the
evaluator's walk (`for_each_binding`) does.

Append and concatenation convert a function TLC keeps lazy with FcnLambdaValue.toTuple after
both operands evaluate. For proved unenumerable Nat, Int, STRING and Seq domains, the evaluator
reports the conversion failure with the Append or Concat Java method signature, without
evaluating the function body (sequence-lambda-* startup fixtures, recorded from d8fb231).
Unknown domains and unproved startup ordering with mixed-set sibling operands still decline.

Configuration name tokens retain the raw quoted image TLC reads; ordinary string constant values retain their decoded value. Quoted directive, assignment and substitution names now follow the same lookup as the jar. A quoted SYMMETRY name can still decline where its validation is unsupported.

`k :> v` holds direct Nat, Int and STRING operands as values, just as a set enumeration does. TLC's `MakeFcn` constructs its singleton function without enumerating either operand, so these values can occur in its domain and range and print successfully. Seq operands retain their existing enumeration decline.

A failed startup definition can also be retried when its direct syntax proves one infinite built-in value is the operand of a supported numeric, relational, sequence, merge or function-application operation, with only scalar literals or empty/singleton literal sets as its other operands. The existing effect check still applies. Nested set algebra, aliases and predicates retain their earlier confirmation guard; the failure reason by itself does not prove that TLC would retry before reaching another failure. The direct and rejected nested shapes have jar-recorded startup fixtures.

A startup @@ expression with a direct Nat, Int, STRING or Seq value can be retried where its
other operand is a proved total value constructor. The proof covers homogeneous literal scalar
sets, tuples and records, valid literal intervals, sets built from proved sets, singleton
functions and bags of literal sets; a single empty function domain proves its body is not run.
Nonempty functions, maps/filters, logical set operations, heterogeneous sets and named
definitions keep the earlier guards. Retry eligibility, effect equality and the four admitted
infinite-enumeration engine failures remain unchanged. The real argument conversion/type
failure is independently replayed (startup-merge-* startup fixtures, recorded from d8fb231).
The total-constructor admission proof uses an iterative worklist with separate Set and Argument
requirements, memoized per resolved node and requirement. Deep syntax consumes heap worklist
space rather than the Rust call stack; tuple arguments cannot thereby become set operands.

Membership against a directly written mixed scalar set evaluates its elements in written
order and tests each held element against the candidate. A direct mixed scalar set reduced
against Int, Nat or STRING likewise tests its held elements in order and fails at the first
incompatible type. No unsorted result enters the store. Aliased sets and other reducers
retain the existing normalization and replay guards (`written-*` startup fixtures).

Mistyped membership diagnostics follow ordinary Java `Value.toString()` with
`swallow=true`: a lazy expansion failure falls back to rendering its captured operands.
A SetEnum normalization failure in that fallback precedes the final kind-error text.
Known Subset, function-set, record-set and product receivers use this physical-class
replay only under the explicit pinned runtime and an affirmative closed Java producer
context, including every imported module and both override indexes. Opaque, unknown and
legacy contexts retain their previous membership path. The evidence that the standard modules'
sources are the pinned ones is taken once, before lowering, and checked again as the lowered model
is published: where the module source reads no longer show those sources, a model that relied on
them declines (`standard module source reads changed before metadata publication`). Instances in theorem statements,
proofs or module USE/HIDE expressions likewise keep the old path until the runtime module
inventory covers those contexts, including nested proofs and NEW bounds. The replay never
evaluates a filter predicate or a held function body. All 416 historical
union-grid exception cells now require native Jar answers. `member-display-*` startup
fixtures pin expansion and fallback failures, including an unsizeable first operand and
written function-field order.
The new replay excludes Any-valued graphs. Function-set domains need scalar keys or a
proved size failure before enumeration, such as SUBSET Nat: its size calls Nat.size first.
Java's generated functions share a domain array; mathematical enumeration can otherwise
compare an exceptional key that Java skips. Unproved graphs retain their old path.
The unnormalized-record DOMAIN reduction cases now hold the record's names as written where the
record constructor is written in place as DOMAIN's operand (the grid's 149 cells match); a record
bound by a LET or built by EXCEPT stays in the known-wrong ledger.

A direct `PrintT(S \ T)` whose `S` is syntactically a non-enumerable value, or
`PrintT(S \cup T)` with a non-enumerable operand and no possibly empty reducible
operand, can retry a failed constant evaluation before effects. TLC necessarily fails
while deep-normalizing or printing that value. The certificate excludes effects in
operands, state reads and enclosing expressions, and retains independent startup replay
confirmation and the existing use-site guard for failures reached through a function
construction. The certificate proves that startup fails; those replay guards determine
whether the same first failure can be reported. Empty set union bypasses the lazy
wrapper and keeps the existing guard.

Len, Head and Tail first convert a function TLC keeps lazy with `FcnLambdaValue.toTuple`.
For a single-bound function over Nat, Int, STRING or Seq(S), its unenumerable domain fails
before the method checks for a non-sequence or evaluates the function body. The trace evaluator
reports that conversion failure with the method signature and return type of the overridden
Java method (`lazy-sequence-*` startup fixtures, recorded from TLC at d8fb231). Other
unenumerable domains remain declined where the tuple-conversion helper does not know the error.

Default diagnostic formatting also follows finite lazy power sets, products, record sets and
function sets when both their components and unchecked formatting are proved successful. This
includes symbolic output above TLC's expansion bound and empty products or function sets. A
failed component or unchecked-format proof remains a decline: default formatting may swallow
the error, or successful empty expansion may never read the offending component. The shared
guard applies to Append, concatenation and @@ diagnostics (`finite-default-*` startup fixtures,
recorded from TLC at d8fb231).

The specification reader preserves the configured property name through temporal decomposition. It prints TLC warning 2258 when the single configured property accounts syntactically for every temporal constraint, using the configured override target's definition location. Extra fairness constraints, multiple configured properties, an equal formula under another name, and TLC's special [] decomposition retain the jar's warning behavior (`fairness-tautology-*` startup fixtures, recorded from TLC at d8fb231).

The trace evaluator words TLC's incompatible-kind comparison or equality error for a function, tuple or record on the left only where the physical Java class, default text formatting and retained domain order of both arguments are known. It leaves sets, unsorted sets, unknown interval and overridden-set provenance, lambdas, ambiguous function order and uncertain formatting unsupported. A set enumeration whose sort fails as that diagnostic words it, as `{7, <<5, 6>>}`, is held unnormalized as any other set TLC fails to sort: its consumers sort it as `ValueVec.sort` does, each new element the receiver of `compareTo`, or search it as written, each element the receiver of `equals`, as TLC does (the neighbours probed against the jar, of sets of tuples, records and functions beside scalars under cardinality, CHOOSE, quantifiers, memberships, equalities, set operations, function constructors and prints in every context, match or decline). Three consumers TLC treats otherwise decline. A function constructor over such a set, or over any set TLC fails to sort as the function of an application, TLC keeps lazy (`FcnLambdaValue`) and applies searching the domain as written (`SetEnumValue.member`, each element the receiver of `equals`), so `[x \in {7, <<5, 6>>} |-> x][7] = 7` holds there and `[x \in {1, "a"} |-> 0][1]` is 0, where the evaluator sorts the domain ("a function over a set TLC fails to sort"; the latter was wrong on main alike). A filter or a set map of a set TLC fails to sort, past TLC's startup, TLC fails on as it fingerprints the state, a FingerprintException with its own stack, where the evaluator fails as it enumerates ("a filter or map of a set TLC fails to sort, in a state"; `S == {1, "a"}` with `{x \in S : TRUE}` was wrong on main alike), and a replay that reads such a set from a definition computed before it now notes it as one it built, as `S == {7, <<5, 6>>}` with `CHOOSE x \in S : TRUE` in a state ("a set TLC leaves unnormalized"). A state TLC fails to fingerprint whose printing normalizes such a set, inside a lazy set's text too, as `{s \in SUBSET {1, "a"} : TRUE}` in Init, TLC reports as an exception it didn't expect, where the evaluator printed the set as written ("a state that holds a set TLC fails to sort as it prints it"; wrong on main alike). A newly worded failure while replay fully enumerates a lazy union for subset testing stays unsupported because TLC can decide on an earlier element.

Print and PrintT copy and deep-normalize their arguments, but TLC's lazy binary-set values retain operands on deepCopy. The replay follows that normalization only for a direct syntactically fresh difference of a directly constructed function/record set and enumeration of literals, with no calls, names, effects, repeated nodes or nested set operators, and only when physical classes and the recursively held values are known. For an unproven operand it retains the previous function-comparison behavior during Print settlement and formatting; physical class metadata alone does not prove that a lazy set has no cached enumeration. CLI tests record direct function/record differences and a successful cached shared-argument case against TLC at d8fb231. Other parameterized or cached lazy print shapes remain as described by the known-wrong-output entry; do not remove that entry as a whole.


A set applied as a function reports TLC's non-function diagnostic when replay has
retained its physical value class. Enumeration contents cached for a set do not
change that class. A transfer that loses the class still declines this new
admission; existing lazy-set diagnostics retain their earlier behavior.

SANY handles a function bound that uses its own name and repeated VARIABLE declarations;
the latter keeps the first state slot and location after reporting the warning. Module
openers accept JavaCC's spaces before MODULE, and EXCEPT !.@ reports the parser error
even in an otherwise parsed expression. Monolithic module extraction follows Java
BufferedReader line endings without adding a blank line at EOF. These cases have
pinned-jar fixtures; the unrelated EXCEPT missing-field warning still differs.

Boolean demands name the physical class of sets and functions only when proved. An eager
function-record diagnostic requires direct construction or proven reducible domains;
materialization alone does not establish that a lazy function changed its Java class.
Unproved materialized functions retain their existing decline.

The configuration tokenizer recognizes SANY's based numeral tokens, longest symbol tokens
with their original spelling, and nested block comments. `ModelConfig.parseValue` passes a
based numeral's complete token image to `Integer.parseInt`, which fails rather than accepting
a binary, octal or hexadecimal configuration integer. Pinned-Jar startup fixtures cover those
errors, malformed digit suffixes, `==`, longer symbols, nested and unfinished comments, and the
order of configuration errors, SANY errors and startup effects.

A global assignment of a user definition gives the configuration name an initial Value, even
when the written definition takes arguments or mentions state. INIT and NEXT reject that Value
before checking operator arity; SPECIFICATION reports its value. Scalar assignments of actual
bundled Java operators also preserve their original arity for direct and higher-order calls:
the assigned value is returned without evaluating arguments. A substitution that captured the
original Java method keeps that method; this uses its actual registered module and a closed
provider origin, not its spelling alone. Core operators that are not root definitions ignore
such assignments as TLC does.

The initial assigned-value facts are not a complete mutable `defns` table or a startup cache
witness. A newly recognized configured SPECIFICATION after an effectful startup definition
still declines (`a configured SPECIFICATION value after a definition TLC computes with its
effects`). Scoped body assignments, startup publication into an original operator header,
MethodValue selector diagnostics, and VIEW's actual completion remain separate limitations.
Fifteen original-arity probes now retain the original positive-arity OpDef header before a
scoped body assignment is read. Positive arity prevents the startup value publication that can
replace a nullary header; it does not establish the state of a nullary definition or its body.

Twenty-six selector and scope shapes (ten state INIT/NEXT entries, five literal INIT entries,
six selector controls, one invariant diagnostic and four effectful selectors), which main
matches, match the pinned jar at -workers 1 and 4, as do the fifteen arity probes above. A scoped
`K = [M] v` makes v the tool object of K's body (`getBody().setToolObject`), which only
`lookup`, through an application of K or of a copy an INSTANCE makes (through its SubstInNode
body), and `Tool.eval` of a literal body read. INIT, NEXT, an INVARIANT, a PROPERTY and a
(ACTION_)CONSTRAINT take K from `defns`, which the scoped entry leaves alone, and walk its body
as written; `processConstantDefns` skips K, as `lookup` gives v. A function definition
`K[x \in S] == e` is an OpDefNode of arity 0 there too. For a definition without parameters, or
a function definition, that one of these selectors names, `check_selected_scoped_values` then:

- leaves v out where nothing else reads it;
- gives v a key of its own (`K#scoped`) where an application of K reads it, and points the
  applications at that key, so the selector reads K's body and `Inv == K` reads v;
- keeps v under K's key, as before, where an INSTANCE of K's module copies K and something applies
  the copy; the selectors then read a K above constant level by its definition, and decline one
  of constant level, but a PROPERTY that isn't in a LET's INSTANCE;
- keeps v for a numeral or string K that only a PROPERTY names with v TRUE, which TLC's implied
  initial predicate reads as TRUE, under K's key, which `get_config_predicate` reads for a K a
  module the root extends defines (`P == 2` in E, `CONSTANT P = [E] TRUE`) as for one the root
  defines (`scoped-property-*-extended`);
- declines (`a module-scoped configuration value of a definition the configuration also
  selects, where TLC may read the value`) where K's name is in another part of the
  configuration, or where it would keep v for a K the root module defines, whose key is its name;
- declines (`a module-scoped configuration value of a definition an unnamed INSTANCE copies
  under a name the configuration selects`) a scoped entry of a module whose K an unnamed
  INSTANCE copies into the root module, where the selector reads the copy.
- declines (`a module-scoped substitution of a definition an unnamed INSTANCE copies under a
  name the configuration selects`) a scoped substitution `K <- [M] Q` alike: the selection
  evaluates the copy's own body (`def.getBody()`, a `SubstInNode` over the body that holds Q's
  node, which an OpApplNode ignores), and every reference to K, the copy's too, reads Q
  (`lookup` follows the `SubstInNode`). With `P == x < 2` and `NextB` printing P in Base,
  `INSTANCE Base`, `Q == FALSE`, `CONSTRAINT P` and `P <- [Base] Q`, TLC constrains by x < 2
  and NextB prints `<<"P", FALSE>>`; main and the earlier front end reported `The constraint of
  P is equal to FALSE` for every Q (`c_base_*` probes, 5 runs).

For a K of constant level, which TLC doesn't compute at startup but the front end does,
`check_scoped_selection` answers only a pure body that fails to evaluate, a pure body equal to
TRUE as a PROPERTY or a (ACTION_)CONSTRAINT, a literal body as INIT, and a literal body (not an
unnamed INSTANCE's copy, whose error shows the INSTANCE's location) as an INVARIANT or a PROPERTY
where v isn't a boolean; it declines the rest (`a module-scoped configuration value of a constant
definition the configuration also selects`). A PROPERTY's body is walked as `processConfigProps`
walks it, so a \A over the empty set, reached through a conjunction, a LET, an operator's
application or an interval, stops TLC with `Temporal formula is a tautology` (exit 77) here too.
A function definition that a PROPERTY names declines (`a function definition the configuration
names as a PROPERTY`), with a scoped value or without: TLC rejects the function its implied
initial predicate evaluates to, at locations the front end doesn't show.

On 712 neighbouring models (1,424 runs at -workers 1 and 4: selectors × body levels × values,
extended, root-scoped, two-scope, instance, referencing and global-and-scoped models), and on
1,196 more probe runs (applications from the root, extended and instanced modules, named, unnamed
and LET instances, function definitions, literal and \A bodies under PROPERTY, in the five
contexts), every run main matches also matches here, but one where main matches by chance (an unnamed
INSTANCE's copy of a K of constant level equal to TRUE, as a PROPERTY with the value TRUE, which
main reads for K and is wrong with FALSE and 7), and no run is wrong that main declines or
matches. A Print K equal to TRUE as a CONSTRAINT that something applies declines, where main is
wrong.
The `configured-binding-*` fixtures preserve the pinned Jar's initial Value diagnostics and
higher-order argument effects.

KNOWN WRONG (main and this source): a global `CONSTANT K = TRUE` for a definition K of a level
above constant that an INVARIANT or a CONSTRAINT names. TLC puts the value in `defns`, warns of
the TRUE invariant and drops it, or accepts the TRUE constraint without checking it; the native
checker warns but still checks K's body, so `K == x = 0` reports `Invariant K is violated`
where the jar finds no error. A NEXT whose definition is a state-level comparison such as
`K == x < 2` is also named `<` by TLC (`<< line ...>`) and `K` here, with or without a scoped
value.

An indexed Java alias matches: an actually matched `J.Any()`
returning 42 retains its method when `Any = [J] 7` replaces the scoped body and `H <- Any`
copies the global binding. The check uses the matched Java override and resolved scoped symbol,
not its name alone. Global assignment, direct invocation and copied-method aliases keep their
distinct precedence. Sixteen such alias shapes match, beside the twenty-six action-body cases
above. Initial assigned-value facts still do not
constitute a complete mutable header/body cache or support every method/substitution alias.

#### Scoped configuration entries

The configuration reader resolves `<- [M]` against the external modules, including the root and
standard modules, and checks the operator name, the root module's replacement and its arity in
TLC's order. An inner module is not an external module. A scoped `= [M]` for an unknown module,
an inner module or a name that is not an operator definition is ignored, as TLC ignores it.
Global replacements of an operator node take precedence over a scoped replacement of its body;
scoped replacements of a shared body follow the modules' dependency order, and the last entry
for the same module and name wins. The eleven upstream `config/module_overrides` differences
now match the pinned jar; `scoped-config-*` startup fixtures record the errors and the neighboring
precedence, scalar-operator, collision and rehash cases directly from TLC at d8fb231.

A substitution `X <- Y`, global or scoped, gives X the OpDefNode of Y, whose body TLC
evaluates as written (`Tool.evalAppl`); a scoped entry `Y = [M] v` or `Y(a) = [M] v` sets a
ToolObject on that body, which the evaluation reads only for a literal body
(`Tool.evalImpl`'s NumeralKind, DecimalKind and StringKind), so X reads the entry only there,
a declared constant as well as a definition. For any other body, where nothing in the spec
names Y the entry has no effect, as with `Small = [Scoped] {0}` beside
`Nat <- [Naturals] Small` (`tests/unit/modules.test.ts`) and `Inc(0) = [Op] 7` beside
`F <- Inc` (`tests/unit/operator-constants.test.ts`). A read of Y itself finds Y's own
ToolObject before the body's (`SymbolNodeValueLookupProvider.lookup`), which
`processConstantDefns` sets to Y's computed body where it computes Y through X: for a declared
constant X in the root module's loop over the constants, before any of its definitions, and for
a definition X where a module's loop over the definitions first reaches X, where Y is of
constant level. So, for a global substitution of a nullary Y:

- Where Y's body reads a variable, TLC never computes it, and Y reads the entry everywhere
  (`Small == c < 2`, `Small = [M] FALSE`, `X <- Small`, `Inv == Small`).
- Where no definition TLC computes before Y reads Y, Y reads its body everywhere (`C <- Small`
  with Small defined in the root module; `X == {}` before `W == Small`). Where computing Y's
  body fails there, TLC swallows the failure and Y reads the entry everywhere; the front end
  computes it, and links the spec again with the entry where that fails. Besides what the
  front end's constant evaluator computes and the literals `certainly_computes` names, a
  function whose domain is certainly empty (`{}` or `{v \in {} : p}`) computes without its
  body or p: TLC builds it at once over a reducible domain and lazily otherwise, where
  `deepNormalize` normalizes only the domain, so `A == [i \in {v \in {} : TRUE} |-> 1 \div 0]`
  and the function definition `A[i \in {v \in {} : TRUE}] == 1 \div 0` print `<<>>`
  (`scoped-target-empty-domain-function`).
- Where every definition TLC computes before Y whose value shows fails as TLC computes it,
  reading the entry, and has no effect, TLC computes it again at each use, after it computed Y,
  so every read finds Y's computed body and the entry shows nowhere: the front end computes
  those definitions with the entry, and links the spec again without the entry where all fail
  (`Before == 1 \div (A - 9)`, `A == 1 + 1`, `A = [Probe] 9`, `K <- A` after Before, so
  `PrintT(<<Before, Middle, After, A>>)` prints `<<-1, -1, -1, 2>>`,
  `scoped-target-early-reader-fails`). Where some fail and others don't, it declines.
- A definition TLC computes before Y that reads Y only in the predicate of a set filter
  `{x \in S : p}`, or the body of a function `[x \in S |-> e]`, over a power set reads Y's
  computed body: S isn't `Reducible`, so TLC builds the value lazily (`Tool`'s OPCODE_sso and
  OPCODE_fc) and `deepNormalize` normalizes only S, and the predicate or body reads Y where the
  value is used, after TLC computed Y. That holds where S doesn't read Y, the definition has no
  effects, and no other definition TLC computes before Y names it, which would compute it there
  and keep what it computed (`SetPredValue.toSetEnum`, `FcnLambdaValue.toFcnRcd`): with `A == 1 +
  1`, `A = [Probe] 9`, `K <- A` and `L <- A`, `Before == {v \in SUBSET {1} : A = 9}` prints `{}`
  and `Before == [i \in SUBSET {1} |-> A]` prints `({} :> 2 @@ {1} :> 2)`, where `Mid ==
  Cardinality(Before)` before K makes Before print `{{}, {1}}` and declines
  (`scoped-target-early-reader-deferred`). Only `IntervalValue` and `SetEnumValue` are
  `Reducible`, so the same holds over `Nat`, `Int`, `STRING`, `Seq(S)`, a filter of such a set
  (a filter of a set enumeration or an interval is a `SetEnumValue` OPCODE_sso builds at once,
  so a reader over `{w \in {1, 2} : TRUE}` declines), a set of
  functions, records or tuples (`[{1} -> {1, 2}]`, `[a : {1, 2}]`, `{1, 2} \X {3}`, which TLC
  builds as `SetOfFcnsValue`, `SetOfRcdsValue` and `SetOfTuplesValue`), or a name
  without parameters of the spec's or of a LET (whose definitions don't read Y) for one, as `S ==
  SUBSET {1}` or `LET S == SUBSET {1} IN {v \in S : A = 9}` (`Deferral::is_unreduced`); for a
  function over a set enumeration that is certainly empty, which TLC builds at once without
  computing its body (`[i \in {} |-> A]` prints `<<>>`); and for a name of such a definition as
  its whole body (`Before2 == Before`) or as the set of another such definition (`Before2 == {w
  \in Before : A = 2}`), which hold its lazy value and don't compute it. So do, as another
  such reader, `Before \cup {..}` or `{..} \cup Before` of a set enumeration without effects
  that reads no reader (`SetEnumValue.cup` returns Before where the enumeration is empty and a
  lazy `SetCupValue` otherwise, whose `deepNormalize` normalizes only its operands), `{Before}`
  (one element, which `normalize` compares with nothing), `DOMAIN Before` of a function (its
  domain, `FcnLambdaValue.getDomain`) and `LET L == Before IN L`. A definition nothing shows the
  value of that tests only an element's membership in a filter (`Mid == 1 \in Before`) or the
  filter's elements' in another set (`Mid == Before \subseteq {}`, where the filter's set is
  `SUBSET` of a set enumeration of at most 10 elements or a set of at most 1,024 functions
  between set enumerations, so that TLC's enumeration ends soon), computes the predicate with
  the entry as TLC starts, but `SetPredValue.member` and its enumerator keep nothing
  (`convertAndCache` is only for comparing, counting and fingerprinting the set), so Before
  stays lazy (`Deferral::holds_lazily`, `Deferral::tests_lazily`). Any other use before K
  (`Mid == Cardinality(Before)`, `{Before, {}}`, `Before \cup {A}`, `DOMAIN Before` of a
  filter, which fails, a membership or subset test whose value is printed), still declines,
  though TLC computes some of them lazily too. Such a definition
  counts as one that fails in the item below. A function over set enumerations of at least one element, which TLC builds at once, whose
  body the constant evaluator finds failing at one element fails as TLC computes it (`Before ==
  [v \in {A} |-> 1 \div 0]`, `DOMAIN Before = {A}` fails at the use as main does). So does
  `TLC.Assert` of arguments without effects whose condition the evaluator finds FALSE with the
  entry (`Before == Assert(A # 9, "boom")`): `Assert.fail` throws an `EvalException` that TLC
  swallows without a print, and the use computes it again, reading Y's computed body (`<<TRUE, 2,
  2>>`, `is_rereadable`). One that holds with the entry (`Assert(A = 9, "boom")`), whose value
  TLC keeps, or whose message has an effect, still declines.
- A declared constant K of the root module that the configuration gives neither a value nor a
  substitution of its own fails the model before any read, with `The constant parameter K is not
  assigned a value by the configuration file.` (2222): a module-scoped substitution `K <- [M] A`
  never gives one, so it answers so whatever the entries are, as main does.
- Where every definition TLC computes before Y that reads it fails, or reads Y's computed body as
  above, every read finds Y's computed body, whatever else reads Y: Init, Next or an invariant
  reading `Before` and `A` answers too.
- Where only definitions TLC computes before Y read it, through operators with parameters only
  they apply, each reads the entry, and everything else reads what those computed (`Z == Small`
  in an extended module beside `C <- Small`).
- A read TLC never evaluates isn't one: the branch a literal `TRUE` or `FALSE` condition of an IF
  leaves out, the operands of a junction past a literal that decides it (`TRUE \/ A = 9`, `FALSE
  /\ A = 9`, OPCODE_cl, OPCODE_dl, OPCODE_land and OPCODE_lor stop there), the arms of a CASE
  past a literal TRUE guard or under a literal FALSE one (OPCODE_case), and a LET's definition
  that neither its body nor another of its definitions that is read names, which TLC binds
  lazily (`evalImplLetInKind`); an argument of a parameter the operator's body names only in
  such places isn't read either (`Ig(x) == LET y == x IN TRUE`, `Ig(x) == IF FALSE THEN x ELSE
  TRUE`). A definition TLC computes before Y that reads Y only there doesn't read it, printed or
  not (`Before == Ig(A)`, `Before == CASE TRUE -> 1 [] OTHER -> A`, `ASSUME PrintT(<<Before, A,
  K>>)`), while `A = 9 \/ TRUE` reads it. So a table on a literal body read
  only there shows nowhere (`ASSUME IF TRUE THEN TRUE ELSE C = 7`, `ASSUME LET D == C IN TRUE`
  beside `C <- A`, `A == 2`, `A(0) = [Probe] 7`).
- A Y whose draws decide only whether computing it fails, not the value it gives where it doesn't
  (`A == IF RandomElement({TRUE, FALSE}) THEN 1 ELSE 1 \div 0`, or an ELSE that fails before it
  prints or draws again: one the constant evaluator finds failing, `Assert` of a condition it
  finds FALSE with a message without effects, or a tuple of parts without effects applied
  outside its domain, `<<1>>[2]`, `fails_without_effects`; and a condition whose only effects
  are draws of RandomElement written in it that gives a boolean for every element each draw may
  take, as `RandomElement({1, 2, 3}) = 1`, which the front end's evaluator computes for each
  combination of them, up to 4,096 (`is_boolean_for_every_draw`), also as the guards of a CASE,
  which TLC tests in turn, failing past the last without OTHER (`CASE RandomElement({1, 2}) = 1
  -> 1 [] OTHER -> 1 \div 0`; main answers both at 2 of 12 seeds, as this does, and declines at
  the others, as this does)), with the entry `A = [Probe] 9` and `K <- A` and `L <- A` for
  definitions K and L nothing reads: TLC skips Y where its lookup finds the entry, computes Y
  where it reaches K and again at L, and Y keeps the value of the last computation that didn't
  fail, else the entry. Where nothing else in the spec draws, TLC's computation at K draws first
  from the generator, as the engine's one computation of Y does, so where that doesn't fail the
  value is the one every computation that doesn't fail gives, and Y reads its body (`ASSUME
  PrintT(A)` prints 1 at every seed). Where the engine's computation fails after its draw, TLC
  may yet compute Y at L, or leave it the entry, which the engine doesn't follow: it declines
  (`a definition TLC computes at startup that fails there`, `Definition::NAMED_AT_STARTUP`), as
  main does. That holds without the entry too, where TLC computes Y first where it reaches Y.
- Which value a definition reads doesn't show where nothing reads it but other such definitions,
  it has no parameters, no substitution or configuration name, and applies only builtins without
  effects (no print, register, draw, assertion or file), or it is an operator with parameters
  nothing applies, which TLC never computes. An argument of an operator's parameter the
  operator's body never names isn't a read: TLC binds it to a `LazyValue` (`getOpContext`) it
  never computes. Where every definition TLC computes before Y that reads Y is such, Y reads its
  body everywhere, as where there is none (`Before == Small` that nothing reads, or that only
  `Ignore(Before)` with `Ignore(v) == TRUE` reads, `scoped-target-reader-ignored-argument`); a
  definition computed after Y that is such doesn't count among the other readers of the item
  above (`Middle == Small` and `After == Middle + 1` that nothing reads).
- An entry with arguments for a Y without parameters, as `Y(0) = [M] 7` and Y's only entry, is
  one TLC reads nowhere, before or after it computes Y: Y reads its body everywhere (`C <- A`,
  `A == 1 + 1`, `A(0) = [M] 7` and `PrintT(<<Before, A, C>>)` print `<<2, 2, 2>>`).
- A table on a literal body (`A == 2`, `A(0) = [M] 7`), Y's only entry, which the substitution
  returns as its value and a read of Y applies, shows nowhere where nothing TLC evaluates names
  Y or a name the configuration substitutes Y for, but as an argument of a parameter its
  operator never names (`ASSUME Ignore(C)` beside `C <- A`, `scoped-table-literal-unread`):
  Y's entry is left out. So it is where a name substituted by Y (not Y, whose read applies the
  table) is otherwise read only where TLC computes the table but never looks into it
  (`get_uninspected_parts`): as an element of a tuple whose length `Len` takes
  (`TupleValue.size`), an element of a tuple or a field of a record whose DOMAIN is taken, the
  first element of a tuple `Tail` drops (`Sequences.Tail` copies the others), an element of
  either of two tuples compared with `=`, `#` or `/=` that `TupleValue.equals` tells apart
  first, by their lengths or by first elements that are two different numbers or two different
  strings, and as the whole of an assumption, which fails as TLC expected a boolean value for
  the table as for any literal body (`ASSUME C`, `Len(<<C>>) = 1`, `DOMAIN [v |-> C] = {"v"}`,
  `Tail(<<C>>) = <<>>`, `<<1,C>> = <<2,C>>`, `<<C>> = <<>>`; `scoped-table-literal-uninspected`).
  The same name read anywhere else
  (`PrintT(C)`, `C /\ TRUE`, `IF C THEN ...`, `Tail(<<1, C>>)`, `<<1,C>> = <<1,C>>`, `<<C,1>> =
  <<C,2>>`, `<<1,C>> = <<"a",C>>`, a `Len` the spec defines, `D == C` read as an assumption),
  or beside a print of it, still declines: TLC prints `{ <0, 7>}` or compares it there. Other
  reads TLC never looks into decline too, though main matches them and not by chance: a tuple
  that differs from another at an earlier element of another kind or position (`<<1, C>> #
  <<"b", C>>`, `<<TRUE, C>> # <<FALSE, C>>`, `<<1, 2, C>> # <<1, 3, C>>`, `<<<<1>>, C>> #
  <<<<2>>, C>>`), the length of a tuple built otherwise or nesting C (`Len(<<C>> \o <<C>>)`,
  `Len(Append(<<>>, C))`, `Len(<<<<C>>>>)`, `Len(<<{C}>>)`, `Len(<<[v |-> C]>>)`, `Len([i \in 1..2
  |-> C])`, `Len(SubSeq(<<C, 1>>, 2, 2))`), and an element or field other than C's (`Head(<<1,
  C>>)`, `<<1, C>>[1]`, `[v |-> C, w |-> 1].w`): declines to win back (see "Declines to win back
  where main matches").
- A scoped substitution `X <- [M] Y` sets Y's node on X's body, which `processConstantDefns`
  follows to compute Y where it first reaches X, as for a global one, so the items above hold
  for it where they leave the entry out: with `A == 1..2`, `A = [Probe] 9` and `K <- [Probe] A`,
  `ASSUME A = 9 /\ K = 1..2` fails comparing `{1, 2}` with 9, as A reads its computed body
  (`scoped-substitution-target-scoped-value`). Where they keep the entry for some reads, it
  declines, as the linking reads the entry for X there.
- Otherwise what Y's reads find depends on which definitions TLC computes before Y, which
  isn't followed, and that declines (`a substitution whose target has a module-scoped value the
  spec reads otherwise`), as does a table on a literal body that something reads, which the
  substitution would return as its value, and an operator with parameters. With
  `Small == 0..3`, `Small = [M] {0}`, `X <- Small` and `PrintT(<<X, W, Small>>)`, TLC prints
  `<<0..3, {0}, 0..3>>` where `W == Small` comes before `X == {}` and `<<0..3, 0..3, 0..3>>`
  where it comes after; main prints the latter for both, so it matches the second by chance.

An INSTANCE with substitutions copies a definition into a node whose body is a `SubstInNode`
over the definition's body, which holds a scoped entry's value. A read of the copy finds the
value through the `SubstInNode` (`lookup`), so a table applies there, as the front end's alias
of the copy does (`Attempted to apply the operator { <0, 7>} with wrong number of arguments`),
but a substitution `K <- A` of the copy evaluates its body (`evalAppl`): a literal body returns
the table as its value (`{ <0, 7>}` for `PrintT(K)`), and another body ignores it (`Av == C`
prints 7). The alias doesn't follow that, so such a substitution of a copy of a definition with
a module-scoped table declines (`a substitution whose target is an INSTANCE's copy of a
definition with a module-scoped table`, `scoped-table-instance-copy-*`); main declined those that
read K's value. Where nothing does, the value shows nowhere and it answers, as main does: where
nothing TLC evaluates (a definition, an assumption, an INSTANCE's substitution) names K, or names
it only as an argument of a parameter its operator never names or in an IF's branch a literal
condition skips (`references_shown`), the configuration names K nowhere else, and the copy's
body has no effect (`is_without_effects`), `processConstantDefns` computes the substitute as TLC
starts, swallowing a failure, and drops it (`ASSUME TRUE` beside `K <- A` or `K <- [Probe] A`,
`ASSUME Ignore(K)` with `Ignore(x) == TRUE`, `ASSUME IF TRUE THEN TRUE ELSE K = 2`, with K
declared or defined, at one or four workers; `scoped-table-instance-copy-unread`). A body that
builds a function with `:>` or `@@` has no effect either and answers (`A == [i \in {1} |-> 2] @@
[i \in {2} |-> 3]`). A body that prints (`A == PrintT("p")`, which TLC prints as it starts, where
main prints nothing; `scoped-table-instance-copy-print`) or draws still declines: main matched
`A == RandomElement({2, 3})` with nothing else drawing by chance, as with `ASSUME
PrintT(RandomElement(1..30))` beside it (`1..31`, `1..40`, `1..17`, through `R ==
RandomElement(1..30)`, with or without `Unused == K`) main prints another number than TLC in all
six. A definition that names K, though nothing reads it but a definition of no parameters that
nothing names (or that only a global configuration substitution `Foo <- Unused` names, of a Foo
nothing reads either), whose body has no EXCEPT and no effect but through ToString, TLCEval,
TLCGet (whose minimum level of 1 keeps TLC from computing it as it starts), TLCSet (which fails
there, with neither a checker nor a simulator to set the register of, and which
`processConstantDefns` swallows), `:>` or `@@`, which TLC computes as it starts and drops
(`Unused == K`, `Unused == K + 1`, `Unused == K \div 0`, `Unused == TLCSet(1, K)`, also beside
`ASSUME PrintT(TLCGet(1))`, `Unused == ToString(K)`, `Unused == TLCGet("level") = K`), answers as
main does; a string compared, printed or evaluated (`ASSUME TLCEval("Unused") = "Unused"`) names
no definition. One with an EXCEPT (`[K EXCEPT ![0] = 1]`, which may warn as TLC computes it) or
named only by another such definition (`Un2 == LET z == Unused IN 1`) still declines, a decline to
win back: main matches those, as nothing shows K. A scalar entry (`A = [Base] 9`) the substitution
of the copy reads as TLC does.

`initializeModConstants` builds each module's table of scoped entries as `makeConstantTable`
builds the global one, after the root module's constants are checked: a row of an operator's
table after a value for the same name in the same module (`A = [Base] 9`, then `A(0) = [Base]
7`) fails casting the value to an `OpRcdValue`, as for global entries
(`scoped-table-after-scoped-value-cast`). Where more than one module's table fails, TLC reports
the first in its Hashtable's order, which isn't followed (`module-scoped tables of more than one
module that TLC fails to build`).

The front end confirms each level it took with the level analysis, declining where they differ.
Main read the root module's scoped entries nowhere, so it matched the unnamed shapes by chance
and is wrong where the spec names Y without a substitution (`Small = [M] {0}` with an invariant
`c \in Small`).

A definition X the configuration replaces by a definition Y of constant level that draws
(`K <- A` with `A == RandomElement({1, 2, 3})`) makes `processConstantDefns` compute Y again
where it reaches X, whatever came of computing Y before, so Y keeps the value of its last
computation and every later draw TLC makes as it starts, and in the initial states, which draw
on from the same generator, comes later; the engine computes Y once. Where the draws decide more
than whether Y fails (`IF RandomElement({TRUE, FALSE}) THEN 1 ELSE 2`, which TLC prints as 1
where the engine prints 2 at `-seed 2718281828`), something reads X, which TLC computes again at
each read, or something else draws (`B == RandomElement(1..1000)`, `Init == x =
RandomElement(1..1000)`, which TLC draws after K's draw), it declines (`a configuration
substitute with effects, which TLC computes again where it reaches the definition it replaces`).
Main answered these without the second computation and was wrong at most seeds; it matched only
where the draws happened to agree (see "Declines to win back where main matches"). KNOWN WRONG
(main and this source): a print in such a Y (`A == PrintT("a")`, `K <- A` with K after A and
nothing reading K) shows again where TLC reaches K, so TLC prints `"a"` twice and the binary
once; where K comes before A, TLC computes A at K, keeps its value and skips A, and prints once,
as the binary does.

A definition the configuration replaces by a definition of constant level that prints
(`X <- Small` with `Small == Print("p", 3)`) reads Small's OpDefNode, which TLC evaluates at
every read of X, besides computing it as it starts; where TLC may evaluate a read of X, that
declines as a declared constant's does (`a configuration substitute with effects, which TLC
evaluates at every use`). A read in a branch a constant condition leaves out (`FALSE /\ X`,
`FALSE => X`, `IF 1 = 2 THEN X ...`, `\E i \in {} : X`) isn't one, as for a declared constant.
An ALIAS nothing else names TLC evaluates only as it prints a state (`Tool.evalAlias`), and then
prints X's substitute again at each state of the trace, which the engine doesn't follow: a run that
reads X only through such an ALIAS answers where it finds no error and declines a trace, a
simulation and a dump (`a trace printed through an ALIAS that reads a configuration substitute with
effects, which TLC evaluates at every use`). main prints such a trace without the reprints.

A scoped substitution `K <- [M] T` whose target T TLC replaced with a Java method holds the
method in `defns`, not an OpDefNode, so `processSpec` skips its arity check
(`this.defns.get(rhs) instanceof OpDefNode`) and K's body takes the method as it is: Len, Append,
SelectSeq, Cardinality, BagToSet, ToString and the other bundled methods, TLCGet, TLCSet, and a
user class's matched methods. A global substitution for T puts the value of its own target in
`defns` first (`Len <- Foo` with `Foo(a)` makes `K <- [M] Len` with nullary K report 2225), and a
global value `Len = 4` gives way to the method, which `processModuleOverrides` puts in `defns`
after it. Where K's arity is the method's and T has a global value, K reads the method
(`\0configuration-defns:` as for a global substitution); where the arities differ, applying K
fails in the method (2154, `handle's method type ... but found ()Value`, `array is not of length
2`), which isn't modelled, so K is a builtin that declines where it is applied (`the builtin K@M,
whose value the interpreter computes`), and a spec that never applies it answers. The same holds
for a global value of T with a user class's method. A scoped value `TLCSet = [TLC] v` no longer
replaces TLCSet's method: TLCSet's `@TLAPlusOperator` arity check compares the method with the
OpDefNode's own arity, which the entry leaves as written, so the method installs on the body after
the entry as the other closed methods do (`config-scoped-*` startup fixtures).

A substitution of a user definition for TLCSet or TLCGet, scoped (`TLCSet <- [TLC] Foo`) or global
(`TLCGet <- G`), gives the name the level of that definition's body: `getLevelBoundAppl` looks the
operator up first and finds the OpDefNode, not the method, so with a constant Foo an invariant
`Inv == TLCSet(1, 5)` is constant-level, computed as TLC starts, and reported there
(`The invariant of Inv is equal to FALSE`, or the 2149 warning where it's TRUE), as the front end now
counts it. main counted it state-level and reported it at the initial state. A substitute that
prints still declines (`a configuration substitute with effects`).

TLC's `defns` holds no THEOREM or ASSUME name (a `ThmOrAssumpDefNode`), so a substitution whose
right-hand side, global or scoped, names one reports `The configuration file substitutes for F
with the undefined identifier T.` (2224), and one whose left-hand side names one reports that the
identifier does not appear in the specification (2226). A name of INIT, NEXT, SPECIFICATION,
INVARIANT, PROPERTY, CONSTRAINT, ACTION_CONSTRAINT, VIEW, ALIAS, SYMMETRY, POSTCONDITION or the
other sections that names one TLC reports as not defined, in an order the front end doesn't
follow from where it checks, which declines (`a configuration entry that names a THEOREM or an
ASSUME`). main answered all of these as if the name were a definition.

TLC's lookup of a name the configuration substitutes a definition Y for finds Y's OpDefNode, not
the value `processConstantDefns` computed and deep-normalized for Y, and `Tool.evalAppl`
evaluates Y's body as written at each read: a set it enumerates is a new SetEnumValue TLC holds
unnormalized, with a source, whose `member`, `diff` and `cap` search and iterate its elements as
written (`ValueVec.search` with `equals`), and whose failures a FingerprintException traces. The
lowering gives such a read a copy of Y flagged `CONFIGURED_SUBSTITUTE`, which the trace evaluator
computes from the body at each read rather than taking Y's startup value: `CONSTANT Int <- Z`,
`Z == {1}`, `"a" \in Int` reports checking equality of integer 1 with "a", as TLC does, for a
declared constant and a definition alike, in every context. A read through an INSTANCE's copy of
a module-scoped substitution (`Z <- [Inn] Y`, read as `I!Z`) still takes Y's startup value and
compares; see "Known wrong outputs".

An effective global or scoped override whose target body itself has an effective scoped
operator replacement declines
(`a global override whose target has a module-scoped override`, `a scoped override whose target
has a module-scoped override`). TLC can fail with an unexpected `OpDefNode`-to-`Value` cast while
evaluating that target; the native environment does not yet preserve the distinction between
an operator node's replacement and its body's replacement along such a chain. A target that is a
copy an INSTANCE with substitutions makes of such a definition declines alike: with `INSTANCE
Base WITH C <- 7`, `A == 2` in Base, `CONSTANT K <- A` (or `K <- [Probe] A`) and `A <- [Base] B`,
TLC fails with that cast evaluating `ASSUME PrintT(K)`, where the checker reported no error (main
reports a configuration error). The cast is that of a numeral, decimal or string body
(`Tool.evalImpl`'s NumeralKind) returning the replacement: the substitution's `evalAppl`
evaluates the target's body as written, which an OpApplNode body does without the replacement.
So where the target T of `J <- T` (or `J <- [M] T`) has such a body, no parameters, no other
entry and no copy, and nothing TLC evaluates names T but the configuration (whose selections take
`def.getBody()`), T's own replacement `T <- [N] S` shows nowhere, where S has no effect that
`processConstantDefns` would show computing it through T, and the front end leaves it out: with
`K == TRUE`, `B == FALSE`, `K <- [Probe] B`, `J <- [Base] K` and `INVARIANT K`, `ASSUME
PrintT(I!J)` prints TRUE (`scoped-override-chain-*`). main read T's body there too. S's effects
show as those of any definition TLC computes as it starts only where T is computed first:
`processConstantDefns` computes T's own body in the loop of the module J's entry is in (`lookup`
of J finds T's node), so the root's loop finds T computed and S is computed once as its own
definition (`B == PrintT(7)` before or after `K == TRUE` prints 7 once, then TRUE). Where T is
above constant level or fails as TLC starts, the root's loop follows T's body to S and computes
S again where S came first: `B == PrintT(7)` before `K == x = 0` or `K == (1 \div 0) = 1` prints
7 twice, where main prints it once (`scoped-override-chain-state-read`, `st_p_bk`, `dv_p_bk`).
So an S with effects answers only beside a boolean literal T of the root module whose entries
are of other modules or for declared constants, and declines otherwise; main matched the rest
(`st_*_kb`, `eq_*`, `st_r_*`, `st_s_*`, 21 probes) only by the order of the definitions or an
effect whose repeat doesn't show. T and S may read variables, which SANY's levels, that TLC's configuration checks read,
don't see through J's entry to; but neither may be above state level: with `K == x' = x` and
`Inv == I!J` as an INVARIANT, TLC evaluates x' in the invariant and fails (`the identifier x is
either undefined`), where the front end's levels, which follow the substitution, report an
invariant that isn't a state predicate (main reports that too, wrong). Those decline, as do
the 11 probes of an action-level T or S (`sp_*`, `sb_*`) main matched only where no level check
reads J (`sp_invd`, wrong on main). Independent
same-named operators, globally shadowed scoped entries and scalar body replacements do not
trigger this decline; their pinned-jar fixtures cover each relation. The two fixtures
keep TLC's output as `jar.out` beside the explicit decline.

A module-scoped substitution `K <- [M] Q` sets Q's OpDefNode on the body of K's definition
(`opDefs[j].getBody().setToolObject`), which a reference to K reads (`lookup` finds the body's
object and evaluates Q's body). Where TLC evaluates K's body itself, it doesn't: a name the
configuration selects (INIT, NEXT, SPECIFICATION, INVARIANT, PROPERTY, CONSTRAINT,
ACTION_CONSTRAINT, VIEW, ALIAS, POSTCONDITION and the rest take `def.getBody()`) and a name it
substitutes for another (`X <- K`, whose `evalAppl` evaluates the OpDefNode's body). An OpApplNode
body ignores the object there, so `INVARIANT P` with `P == x < 2`, `Q == TRUE` checks `x < 2`;
a numeral, decimal or string body returns the object as its value (`Tool.evalImpl`'s
NumeralKind), which fails with an unexpected ClassCastException ("class
tla2sany.semantic.OpDefNode cannot be cast to class tlc2.value.impl.Value") but where the
substitute is a Value (an assigned Q, a Java method, a builtin's value). `processConstantDefns`
follows `lookup` to Q too, so it never computes K, and `defns` keeps K's node. The front end
reads the substitute for every reference, so where nothing TLC evaluates but the selection
names K (no assumption, no other part of the configuration, no definition of constant level
TLC computes as it starts where Q's or K's body has an effect), it drops the substitution and
marks K as a selected definition whose module-scoped entry `defns` doesn't hold, which
`check_scoped_selection` already treats as TLC does. A definition TLC computes as it starts
that names K but nothing reads (`getLevelBound` and `lookup` follow K to Q) shows only where it
has an effect and Q is of constant level, as `R == PrintT(P)` prints Q's value as TLC starts
(`scoped-substitute-selected-startup-print`), which declines; main and the native checker
printed nothing there, which matched TLC only where computing Q failed first.

A (ACTION_)CONSTRAINT K is the exception: `processModelConstraints` and
`processActionConstraints`, the last steps of `processConfig`, set K's own node on its body
(`body.setToolObject(toolId, def)`) in place of Q, so every reference TLC evaluates after that
reads K's body, as the selection does: with `P == x < 2`, `Q == FALSE`, `CONSTRAINT P` and a
next-state relation printing P, TLC prints TRUE (`scoped-substitute-constraint-read`). What
reads Q before is `processConstantDefns` and `processConfigSpec`, which walks a SPECIFICATION's
or a PROPERTY's references by `lookup`; so where K is above constant level, the configuration
has neither, Q has no effect, and no definition TLC computes as it starts that names K is read
or has an effect, the front end drops the substitution for a K that is also read, and declines
otherwise (`scoped-substitute-constraint-startup-reader`).

It declines (`a definition the configuration names whose body a module-scoped substitution
replaces`) where any other K is both selected and read, where the configuration substitutes K
for another name, where K's body is a literal without a Value substitute, and where K has
parameters or another entry. A module-scoped substitution `J <- [M] K` whose name J the configuration also sets for every module (`J = 7` or
`J <- B`) substitutes nothing, as that setting shadows it (the `scoped-config-global-lhs-*`
startup fixtures), so it doesn't count as substituting K. main ignores a
module-scoped substitution, so it is wrong wherever a reference reads it (`Init == x = 0 /\ P =
2` with `P == 2`, `Q == TRUE` fails on TLC comparing TRUE with 2) and wherever the literal's cast
fails, and matched a selected and read K but a (ACTION_)CONSTRAINT only where Q and K's body
agree on the states it reached (`INVARIANT P`, `Init == x = 0 /\ P`, `P == x < 2`, `Q == TRUE`,
now declined; with `Q == FALSE` and a next-state relation printing P, TLC prints FALSE where main
prints TRUE). Before,
the native checker read Q for the selection: `INVARIANT P` with `P == x < 2`, `Q == TRUE`
printed "No error has been found" where TLC reports the invariant violated, and `PROPERTY P`
with `P == 2`, `Q == TRUE` and CHECK_DEADLOCK FALSE did too where TLC fails with the cast.

A scoped entry for a module an INSTANCE in a LET instances with parameters (`K = [fx] 5`, `Q(2) =
[fx] 50`, with `LET I == INSTANCE fx WITH N <- 3 IN I!Get`) is read as TLC reads it. TLC sets the
entry on the body of the module's definition (`SpecProcessor.processConstantDefns`), and
`SymbolNodeValueLookupProvider.lookup` looks through the `SubstInNode` of each copy SANY makes for
the LET to it, so `I!Get` reads 5 and `I!Q(3)` fails on the table `{ <2, 50>}`, without a frame at
the INSTANCE. The front end's copies have keys of their own, which the entry doesn't reach, so the
spec is linked a second time with each copy of a definition the entry names (through any number
of copies, named or in a LET, as `I!J!Get` with `J == INSTANCE fx WITH N <- M` in the module the
LET instances) reading the definition. The name the INSTANCE exports without arguments is the
exception: `LetInNode` binds `I!K` to a `LazyValue` of its own body, which `Context.lookup` finds
first, and which reads the entry only where the body is a literal (`Tool.evalImpl`'s NumeralKind,
DecimalKind and StringKind): with `K == N + 1`, `I!K` is 4 and `I!Get` 5; with `K == 1`, both are
5; `I(p) == INSTANCE ...` takes arguments, so `I(2)!K` is 5. main read the copies' bodies (`| 1`
for `I!Get`, a false "No error has been found" with `I!Get = 5`), and matched only where the
copies read nothing the entry names. A module-scoped substitution for such a definition (`K <-
[fx] R`, where TLC fails with the cast of an `OpDefNode` to a `Value`) still declines, "a
module-scoped substitution for a definition an INSTANCE in a LET copies"; so does any spec whose
second linking reads other definitions than the first, "a module-scoped configuration entry for a
module an INSTANCE in a LET copies".

An emptiness test of a lazy filter whose first element passes but a later predicate fails still
declines, as on main. TLC's `Value.isEmpty` takes the first element of a `SetPredValue`'s
enumerator, while the engine's `Lazy::is_empty` collects the full stream. Writing S as shorthand
for the inline filter
`{s \in SUBSET {1} : IF s = {} THEN TRUE ELSE 1 \div 0 = 0}`, TLC answers TRUE to
`Cardinality([S -> {}]) = 0` and `Cardinality([S -> {0}]) = 1`, and to a zero-cardinality test of
`S \X {}` or `[a : S, b : {}]`; the native checker declines with `enumerated a lazy filter`.
An empty factor or field before S, an empty function domain, and a direct cardinality of S retain
their matching behavior. This remains a fallback until emptiness checks stop at the first element.

#### Written set enumerations

A constructed `SetEnumValue` retains its written elements until an operation normalizes it.
It remains Reducible before normalization: intersection and difference iterate those written
elements and call the other value's membership method. Their result is another unnormalized
set enumeration, including one whose later normalization fails. A modeled reduction failure
carries that receiver event through startup replay only when both operands' physical dispatch
is known; the other startup, function, map and effect guards still apply.

The evaluator's provisional canonical sort rolls back nested normalization effects. Actual
enumeration, comparison and equality replay the written sort when normalization is observed,
so a nested set's subsequent membership uses the right equality or comparison receiver.
Untyped model values are a separate Java delegation path and do not normalize the set they
compare with. `Permutations` wraps a runtime failure from its own normalization as its Java
method failure, while forwarding an EvalException unchanged. Jar fixtures cover the nested
alias, model-value, reducer-result and method-error boundaries.

#### Any values

The capability belongs to the packaged Java implementation of the operator's source module.
A real external class for that module shadows the packaged class (`TLAClass.loadClass`), even
when the replacement has no Any method, leaving TLA Any's unbounded CHOOSE. Each environment
marks that Any builtin `DECLINED`, and the engine requires that marker absent. Aliases and
INSTANCE copies retain it; a model that never evaluates Any keeps its previous behavior.
No global standard-module metadata is changed. New value consumers require native reporting
and a closed origin; an opaque or non-native TLC Any keeps the previous member-only route.
Indexed overrides still require precise target and initialization provenance before admission.

The new AnySet!ANY alias is enrolled only for an actual locally declared OpDef under explicit
nonlegacy origin evidence. Configured ANY names or copies, and inherited declarations, retain
the old graph until their physical Java replacement phase is proved. Once linking reveals an
opaque complete context, a graph containing this new alias is linked once with alias enrollment
disabled. Both passes retain the same origin, class-byte routing and index evidence. This restores
the old definitions and startup graph. Linking constructs ASTs and metadata and performs static
substitution checks with the frontend evaluator, which cannot execute runtime Print. Static
warning strings belong to the discarded Environment; the replacement precedes runtime startup
evaluation. The enrollment switch permits exactly one retry.

The engine has a dedicated ANY value, separate from the Nat, Int and STRING infinite-set tags.
Membership accepts every value, `IsFiniteSet` returns FALSE, and printing yields `ANY`.
Function-set finiteness asks its domain and range in TLC's order, preserving empty-domain
shortcuts without assuming ANY is nonempty. Equality and comparison retain the receiver's
semantics: ANY compared with a model value is unequal, while self comparison and self
comparison of containers holding ANY fail. Set normalization uses TLC's inserted-element
comparison order. A set constructor does not claim a semantic failure merely because the
engine eagerly normalizes it where TLC keeps its written elements.

ANY has Store kind 10 and comparison-sensitive containment flag 32, distinct from opaque
operator-table values. Rust state transfer uses its own ANY tag 8; the older value encodings
are unchanged, and encoding does not make ANY equality reflexive. The wrapper's existing
unrepresented-value gate is retained. Initial-state fingerprint failures, including ANY in
sets, tuples, records and functions, follow `Value.fingerPrint` and retain the replay's actual
state count. A successor whose plain fingerprint failure also makes TLC's error replay fail
still declines. Under VIEW, retaining ANY still declines until the post-startup classification
of the view definition as an OpDefNode or a computed tool value is proved: allowing it without
that proof would falsely accept `V == {}` where TLC reports configuration error 2233.

Constructed finite sets have written-element reference metadata (`Lazy::Enumeration`), so
cardinality can normalize them at its actual use without requiring their constructor to
normalize. Proven normalization EvalExceptions retain the physical Java exception phase and
exit status. Known UserValues are eager values, even though the trace represents them with the
same enum as deferred set constructions. The existing function/record provenance and scalar
state guards remain in force. A typed model value and ANY can compare differently according
to receiver order, so membership without its normalization phase remains unsupported;
untyped model values are unequal in either order.

Fourteen permanent startup models match the full pinned Jar output at one and four workers,
including initial fingerprints, isEmpty, normalization failures, nonenumerable quantifiers,
function domains, random draws and permutations. Five additional origin fixtures retain the
full Jar witnesses for four capability declines and a prior matching unused-literal case.
A separate 128-state worker pair checks an ANY startup value and its comparison failure after
handover at both native worker counts. On all 221 upstream AnySet and
TLC Any cells, 221 match at both thread counts. The 536 core probes have 466 matches and 70
declines, and the 960 neighbor probes have 560 matches and 400 declines, with no wrong answer
or match lost versus main at either thread count. Shapes whose Java class origin or
initialization the checker can't prove decline.
A failure comparing the sets a lazy set is built of (`SubsetValue.equals`, `Seq(S)`'s range) is
placed by the FingerprintException TLC's value with a source heads, which the replay doesn't
follow ("a failure comparing the sets a set TLC keeps lazy is built of"); under `ASSUME`, where
TLC evaluates with `Tool`, whose values have none, and prints no frames, it is one of the
`UNFOLLOWED_FRAMES`, so `SUBSET A = SUBSET A`, `Seq(A) = Seq({1})` and `[A -> {1}] = [A -> {1}]`
of `A == Any` word TLC's 2155 as main did (27 assume probes match, none answered elsewhere).
Where both sets are built of set enumerations of plain values (numbers, strings, booleans, model
values, and tuples, records, functions and set enumerations of those, which TLC sorted already),
intervals TLC counts, and filters of Nat, Int, STRING or Seq(S) or of such a filter, the
comparison fails, if at all, in the innermost filter's own Enumerator (`SetPredValue.Enumerator`,
which `isEmpty` of a range or a field, or the base's `equals`, reaches, and which the Enumerator
of a filter around it makes as it is made, before any predicate), and `CallStackTool` copies a
filter without its source, so only the receiver's `equals` heads the FingerprintException:
`[{1} -> {x \in Nat : x > 3}] = [{1} -> {x \in Nat : x > 3}]`, a filter of such a filter
(`{x \in {y \in Nat : y > 1} : x > 3}`), a domain of tuples, records, functions or sets
(`[{<<1>>} -> F]`, `[{{}} -> F]`), `SUBSET`, product and record forms, a LET-named one and
`[{1} -> F] = {}` (whose `elements` asks the range's emptiness first) are placed so in every
context, as main did. A part with a source of its own, as `Nat \ {1}` or `F \cup {1}`, or a set
nested in a range, still declines (145 probes in five contexts: 120 match, 25 decline, none wrong;
one shape, `[{1} -> F] = [{1} -> F \cup {1}]`, matched on main and declines, as it did before;
another 37 shapes of filters of filters and of such domains, 330 runs at 1 and 4 workers, match
wherever main matched, none wrong). The power set of such a filter compared with a set that isn't
a power set (`SUBSET {x \in Nat : x > 3} = {}`, `# {{}}`, `= 1..2`, `= [{1} -> F]`, a LET-named
one) converts itself (`SubsetValue.convertAndCache`), whose `toSetEnum` counts it by the
filter's `size`, which fails in the filter's own Enumerator, so the power set's source heads the
FingerprintException once (its `size` and its `equals`), where it declined before; a set
enumeration first (`{} = SUBSET F`), a power set of a power set, or one in a tuple
(`<<SUBSET F>> = <<{}>>`, which main matched) still declines (180 runs, 130 match, none wrong).

#### User classes of standard modules

TLC reports public static methods of a user class for every processed standard module, including
modules reached through imports, before evaluating assumptions. Where that report would appear,
the native command declines (`the reports of a user class overriding a standard module`); it
preserves SANY and configuration errors TLC reports earlier, including an unassigned root constant.
With `-nowarning`, a method known unmatched is ignored, while a matched or uncertain method still
declines. Named INSTANCEs, `LOCAL INSTANCE`, annotated methods, empty classes and inherited methods are covered by
`java-standard-report-*` fixtures recorded with the pinned JAR. Indexed Java overrides remain a
separate limitation.

New Java implementation proofs require definite class absence and the modeled Java launch
profile. Class presence is checked without opening the file; unreadable paths and uncertain
lookup remain unknown. Extra classpath entries, unmodeled VM options and Java environment
options cannot establish that proof. Source-only callers must supply an origin witness to
enable capabilities that depend on the packaged implementation. The legacy lowering probe
can return only an earlier error, never a model with those checks suppressed.

#### State predicates in liveness

Ordinary global predicate calls whose resolved syntax contains only value bindings remain
state or action atoms. The classifier follows actual definitions and known configuration
aliases with a context-aware, cycle-checked expression walk. Scoped calls, recursive or
operator-valued bindings, selections, INSTANCE substitutions and unresolved origins retain
operator expansion; the ordinary-call proof does not establish a general mutable ToolObject
lookup or justify dropping effects.

This preserves the existing EWD687a and SpanningTree answers while retaining higher-order
operator translation. The `ordinary-live-*` fixtures record the pinned jar for global,
parameterized and configured state predicates, higher-order lambdas, local shadows and a
shared definition graph. Constant evaluation of unproved predicate translations still declines.
Printing and warning reproduction that temporal-atom checking cannot support also remain
declined; some printing controls now reach the engine's existing prohibition instead of the
front end's constant evaluator.

`processConfigProps` takes the operand of a property's `[]` as an invariant where
`getLevelBound` finds it below action level, and that bound gives an operator argument level 0
and an operator parameter's application the level of its arguments alone. So
`Outer(G(_)) == G(2)` with `Prop == [](Outer(LAMBDA n : <>(x = n)))`, through a LET operator,
through `Over(F(_)) == F(2)`, or with a named `A(n) == <>(x = n)` in place of the LAMBDA, is an
invariant TLC rejects as it evaluates it (2261, "a temporal formula (<>A) when evaluating a
predicate or action"), where the binary checked it as a temporal property. The front end now
takes the bound where SANY's level is temporal, reading the names an expansion bound as TLC's
context holds them (an argument's expression, an operator argument's body); where that
invariant sits in an instance's scope (`W(H(_)) == [](Outer(H))`, `Prop == W(LAMBDA ...)`) the
engine declines ("an invariant in an instance's scope"), as it did on main's wrong answer.

#### JSON conversion

`ToJson`, `ToJsonArray` and `ToJsonObject` follow the packaged Java override only
where its origin is known. Configured operator tables take precedence over conversion,
including argument evaluation, row lookup and missing-row diagnostics. This also fixes
`ToJson`'s earlier table bypass. A missing table row after a printed next-state argument
still declines where the existing table replay cannot preserve that effect; the table
startup fixtures retain this boundary. Explicit configuration table constructors retain shared
object identity. Their original receiver attachment is distinct from the global lookup entry
that a configuration alias copies after Java overrides. Declared receivers initialize all rows,
including unused results and tables only reached through aliases; unsupported initializer data
declines before startup effects (`an unsupported value initialized before a configuration operator
table is evaluated`). A global alias to an installed Java method keeps that method
even when the original receiver has a table. This lifecycle is admitted only under a closed
resolver namespace with modeled initialization receivers. Unknown or legacy metadata retains
the strict table path. For admitted tables, arguments are evaluated before row data is consulted,
each row's arity precedes key comparison, and a result is read only for a matching row. Missing
IR data and failed interning of nested mixed sets decline only when needed; they do not invent
a row's value or suppress an earlier argument failure. Replay dispatches on retained physical Java classes;
a tuple becomes zero-based object fields for `ToJsonObject`, while a function record
whose domain is exactly `1..n` becomes an array for all three operators. A record is
rejected by `ToJsonArray`, and a set is rejected by `ToJsonObject`. Nested values use
`ToJson` conversion. Runtime failures from normalization and conversion retain the
Java method wrapper; EvalExceptions and argument evaluation failures keep their own phase. Null
inputs report the pinned JVM's null-pointer message. Enumerating a filter for JSON does
not cache its result: another conversion evaluates its predicate again.

The engine handles directly proven tuple, record, function and finite-set constructors,
preserving a directly constructed record's field order for object conversion, `ToJson`'s
among them (`Json.getNode` writes a RecordValue and a FcnRcdValue as `getObjectNode` does), and
writing a directly constructed function's keys in the sorted order its FcnRcdValue holds them,
as `[i \in 0..1 |-> i]`'s `{"0":0,"1":1}`, where its keys are all integers or all strings and its
values hold no key order of their own; keys of other or mixed kinds decline ("a Json conversion
of a function whose keys are of several kinds"), as a model value and the string of its name,
one member of a JsonObject, do. It declines
where the store lost the physical input class or nested key order, a lone surrogate
would be changed by its file-oriented writer, or nesting exceeds 256 levels. Replay
also declines when physical classes, original function order or default key text were
not retained. User `Json.class` implementations and unproved origins remain unsupported.
The `tojson-*` and `json-conversion-*` startup fixtures record the pinned jar's results.
For `IOUtils.Serialize`, replay reports TLC's nested argument error when the third
argument cannot be converted to a record, and the Java null-pointer message if an uninitialized
INSTANCE value is null. It declines when a non-record option contains an uninitialized
literal whose Java formatting is not modeled; initial-state and next-state replay can also decline.
An options record that lacks a format, or whose format is such a null (`RecordValue.lookup` gives
null, which `apply` takes for a missing field), fails printing itself in the message
(`RecordValue.toString`): where a field ahead of any other holding a null is one, the replay
reports that NullPointerException's text, `"r.values[0]"` for the first field it holds and
`"r.values[i]"` past it, in the order the record holds its fields unsorted, through
`Json.textSerialize`'s message; it declines a null nested deeper. A record's field or application
whose value is such a null is likewise missing to TLC, which then throws the NullPointerException
outside any EvalException, so the replay declines it; and the replay of a failure or an assumption
declines wherever its message would print the text of such a null (`print::null_prints`), which
TLC's `toString` never prints. The engine stops at the literal itself, but where what reads a
record or tuple constructor written in place reads none of the nulls it holds: `r.f`, `r["f"]` and
`t[i]` of a field or position written so, that holds no such null; `DOMAIN` of either and `Len`
of a tuple; and the options of IOUtils's Serialize whose `format` is a string other than "NDJSON"
written there (`Compiler::with_null_substituted`). There each null compiles to a value nothing
reads, as TLC's RecordValue and TupleValue hold a null without reading it; the trace evaluator's
`DOMAIN` reads such a constructor too. The null held anywhere else still stops the search: a
LET or a definition bound to the constructor (`LET r == [k |-> N!A, m |-> 2] IN r.m`), an EXCEPT
of it, and `\o` of it, where main, which takes the literal for the value substituted, matches
the Jar only as long as nothing reads the null, and is wrong where something does
(`[k |-> N!A, m |-> 2]["k"] = 2`, `<<N!A, 1>>[1] = 1`, `[k |-> N!A].k = 1`).
The engine takes IOUtils's Serialize as `Json.textSerialize` does: it evaluates the options and the
definition where their format is a string other than "NDJSON", and stops elsewhere, where TLC
writes NDJSON or fails, for the evaluator of failures, which words what fails before the file
opens: a format, open options or charset the options lack or that are of another class, a payload
that isn't a sequence, a file that isn't a string, an open option `StandardOpenOption` doesn't
name, and a file whose directory, or which without CREATE, is missing (`NoSuchFileException`).
`Charset.forName` comes before the open options: a charset name the pinned JVM (Temurin 21.0.13)
knows, as a name or an alias of `Charset.availableCharsets`, in any case of its ASCII letters,
goes on to them; another fails with `java.nio.charset.UnsupportedCharsetException` of the name
where it is a legal one (a letter or digit, then letters, digits and `-+:_.`, `Charset.checkName`)
and `IllegalCharsetNameException` otherwise, as `NOPE`, `""` and `"a b"` do. The two charsets
that only decode (`ISO-2022-CN`, `x-JISAutoDetect`), whose encoder `Files.newBufferedWriter`
makes before it opens the file, decline.
The engine writes NDJSON itself where it evaluates the application exactly when TLC does, on the
file system, with options that are a record written in place whose `format` is "NDJSON" and whose
`charset` and `openOptions` are strings written there: the charset a name of UTF-8, the open
options among WRITE, CREATE, CREATE_NEW, TRUNCATE_EXISTING and APPEND, not APPEND with
TRUNCATE_EXISTING. It opens the file as `FileSystemProvider.newOutputStream` does (no option is
CREATE, TRUNCATE_EXISTING and WRITE; others are as given, with WRITE, so WRITE alone writes over
the start of the file), and writes each element's JSON (`getNode`) on a line of its own, so a
round trip through `ndJsonDeserialize` and APPEND match TLC. Where the model has IOUtils's
Serialize, the engine reads a Json file only where it evaluates the read exactly when TLC does, as
where a model has `JsonSerialize`. A failure, a value it can't convert, and a file it fails to
open stop it before it opens anything, for the evaluator. TLC's walks of the initial predicate, an
action and ENABLED take IOUtils's Serialize as a guard whose value the Java method gives
(`getNextStatesApplEvalAppl`, `enabledAppl`) and walk no body, which the engine's walk and the
evaluator's follow, where both had walked the definition's body: `Next == Serialize(<<x>>, "f", O)
/\ x' = x + 1` failed on `<<"fallback">>` where TLC writes the file, as `main` still does, and so
did a guard named through a LET (`LET W == Serialize(...) IN x < 2 /\ W /\ ...`) or under ENABLED
(`ENABLED (Serialize(...) /\ x' = x)`), in the evaluator. The engine writes no file there, where it
can't tell it evaluates the application exactly when TLC does, so those decline in the evaluator,
and a format other than "NDJSON" there fails on `<<"fallback">>` at the application, as TLC does.
TLC computes a constant definition that reaches IOUtils's Serialize as it starts
(`processConstantDefns`), writing its file once, whether or not the model uses it, and keeps the
value, where the engine would write at each use or never: the front end declines it ("a constant
definition TLC computes as it starts with IOUtils's Serialize"), but where the arguments as
written fail or fall back before the file opens (options that are a number, a string or the empty
tuple, which `TupleValue.toRcd` makes the empty record, or that lack a format, a format other than
"NDJSON" or not a string, a payload or a file that is a number, an open option
`StandardOpenOption` doesn't name, a charset the pinned JVM doesn't know, a file in a directory
that isn't there as the run starts, or not there without CREATE or CREATE_NEW), or a branch TLC
doesn't take (`FALSE /\ Serialize(...)`). The options and their format may be named: a constant
definition without parameters, a LET's, or an operator's parameter given the options at an
application the walk follows (`O == [format |-> "TXT"]`, `LET O == ... IN Serialize(..., O)`,
`Op(o) == Serialize(<<1>>, "out", o)` with `Op([format |-> "TXT"])`), each read as what it names.
Options, a format, or a field TLC computes as it builds the record (arithmetic, a function's
application, a tuple, CHOOSE) that the front end's constant evaluator computes to a failure fail
there too (`1 \div 0`, `[format |-> 1 \div 0]`, `[a |-> 1 \div 0, format |-> "NDJSON"]`), and
options it computes to a record whose format isn't "NDJSON" fall back. Still declining, though
TLC writes nothing: options of a non-empty tuple, a set, a boolean or a CHOOSE, whose failure main
words without TLC's 2169 code; and, which main answers as TLC, a record built as a function of
strings (`[x \in {"format"} |-> "TXT"]`) or by `@@`, the empty function, a LET's operator given
the options as an argument (whose body the walk reads apart from its applications), and an
application the walk can't rule out after one TLC fails at (`Op([format |-> "TXT"]) /\
Op(<<1>>)`). To win those back: compute such options in the constant evaluator, and follow the
order in which a junction's operands fail. `main` writes no file there either, and matches the
transcript only by chance where TLC writes, as an unused `C == Serialize(<<1>>, "f", O)` shows:
the Jar writes the file, `main` doesn't.
A run that declines leaves the file system as it found it: each file IOUtils's Serialize or the
replay of a Json failure writes is kept as it was before the first write, and each directory the
replay makes, and a decline puts them back (`tla_values::written`), so a checker that runs the
model instead finds them as TLC would; a file the run can't read before it writes it declines.
The evaluator writes none ("IOUtils's Serialize with the NDJSON format"), so a replay through such
a write declines, as do READ, `DELETE_ON_CLOSE`,
`SPARSE`, `SYNC`, `DSYNC`, APPEND with TRUNCATE_EXISTING, a model that writes files otherwise or
has startup effects, and options that print. The `NoSuchFileException` is worded only where
the nearest path above the file that is there is a directory: a file or directory on the path that
is there (`Is a directory`, `Not a directory`, a dangling link or another system error) declines.
So does a file that is, holds or is held by a path TLC makes before it evaluates anything, which
the binary doesn't make: the -metadir, -recover or -userFile path, `states` in the working or the
spec's directory, and each dump; and any file under -cleanup, which deletes `states` first.

Configuration tables for `Print` and `PrintT` take precedence over the default Java methods.
Their arguments evaluate in order, then the existing operator-table consumer selects its first
matching row or reports its actual missing-row failure. A table application does not print.
The existing comparison, normalization and diagnostic guards remain in force.

#### Random draws as TLC starts and in a failing assumption

TLC draws from one generator as it starts, seeded with `-seed` (`RandomEnumerableValues`'s
`DefaultRandom` while there is no `ModelChecker`), through `processConstantDefns` and then
`checkAssumptions`. The evaluator of a failing assumption computes the startup with that generator
and keeps it for the assumptions, so a draw in the assumption, or one before its failure, is
TLC's: `ASSUME PrintT(RandomElement({1, "a"}))` fails comparing `"a"` with 1 as TLC does, where
it had declined (`a random draw where the evaluator doesn't follow TLC's generator`).
`SetEnumValue.getRandomSubset` and `IntervalValue.getRandomSubset` make room for the subset
before they draw (`new ValueVec(k)`), which Java refuses for a negative count with a
`NegativeArraySizeException` of the count, so `RandomSubset(-1, {1})` fails with `-1` in the Java
method's wrapper in every context without the generator. `RandomSubset(1, [{1} -> Nat])` fails
with `[{1} -> Nat]`: `SetOfFcnsValue.toString` swallows what counting a part throws, and Nat, Int,
Real and STRING throw as they are counted, once an empty domain is ruled out, so it writes its
parts as they are written. What fails inside the Java methods of RandomElement and RandomSubset
but an EvalException, as the comparison sorting a set enumeration as the method draws from it or
writes it in its argument error (`RandomSubset(1, {1, "a"})`, `RandomElement(<<{1, "a"}>>)`), TLC
reports as the method's failure (2154, `MethodValue.eval`); the evaluator had reported the
comparison alone. `FiniteSets.Cardinality` of a value that isn't a set writes the value in its
2181, which fails where it holds a set enumeration TLC can't sort, in an order the evaluator
doesn't follow: it declines (`Cardinality of a non-set holding a set TLC can't sort`), where it
had written the set unsorted.

Randomization's `TestRandomSetOfSubsets(k, n, S)` has no Java method: TLC evaluates its
definition, `[i \in 1..5 |-> Cardinality(RandomSetOfSubsets(k, n, S))]`, with the arguments bound
to `LazyValue`s, and builds the function where it isn't applied, drawing five times from the
arguments it evaluates once (`FcnLambdaValue.toFcnRcd`), as `DOMAIN` of it does. Applied to a key,
`Tool.evalAppl` keeps the constructor lazy (`EvalControl.KeepLazy`), evaluates the key, and draws
once for it. Its level is `RandomSetOfSubsets`'s, so a constant definition that calls it draws
from the startup's generator, once, and a state's from the generator seeded with the state's
fingerprint. The engine and the trace evaluator follow both, and decline arguments with effects
(TLC may evaluate a `LazyValue` again for each draw), a key outside `1..5` (the failure prints the
function, drawing it whole), any failure of the draws (TLC reports it in the definition's frames,
in Randomization), and a model where the function of another application, or the record of a
field, may reach it, through a definition or a name bound to an argument or a LET's definition,
which TLC may keep lazy there. Where the engine may not evaluate the application exactly when TLC
does (inside a quantifier, a set filter, a function constructor or another place it may evaluate
otherwise), it declines only where it evaluates the application, so
`PrintT(\E x \in {} : TestRandomSetOfSubsets(3, 1, 1..4)[1] = x)`, which TLC never draws in,
prints `FALSE`, as `main` does.

#### Set operations beside an empty set

TLC computes `S \cup T`, `S \cap T` and `S \ T` where one operand isn't a set as long as the
Reducible operand it reduces by is empty (OPCODE_cup, OPCODE_cap and OPCODE_setdiff call the left
operand's method where it is a SetEnumValue or an IntervalValue, else the right one's for `\cup`
and `\cap`): an empty one's `cup` returns the other operand as it is, so `{} \cup 1` is `1` and
`(1 :> 2) \cup (3..1)` prints `<<2>>`, and its `cap` and `diff` return `{}`. `S \subseteq T` with
an empty enumerable S is TRUE whatever T is (`EnumerableValue.isSubsetEq` asks T only of S's
elements). The engine computes these, where it stopped with "a set operation on a value that
isn't a set" or "expected a set", which the trace evaluator's startup then found computing and
declined ("a startup definition the search found failing that computes", 288 runs of the
upstream suite's value matrix). An empty operand the compiled set doesn't know is Reducible, such
as a filter, still stops the engine, as does an operand that isn't a set beside a set that isn't
empty.

The union that returns its operand gives it the union's source in TLC's replay with the call
stack (`CallStackTool.setSource`), and TLC shares scalars (`IntValue.gen`, `BoolValue.ValTrue`),
so after one, a failure in any value's method may be a FingerprintException the replay can't place.
The replay declines that failure ("a failure in a method of a value after a union TLC gave its
source"), as `2 \in ({} \cup 1)` in a step; a failure TLC raises outside a value's method, as
`Cardinality(2..1 \cup TRUE)`, is worded as before. An assumption's failure is worded too:
`checkAssumptions` evaluates with the plain `Tool`, whose `setSource` gives no value a source.

A function constructed over a value that isn't a set, as `[e \in <<2, 4>> |-> e]`, TLC keeps as a
FcnLambdaValue (OPCODE_fc builds one at once only over Reducible domains), which prints as
`[e \in <<2, 4>> |-> <expression ...>]`, and whose DOMAIN is that value. Where a bound's set is
written as such a value (a scalar, a tuple, a record, a function, `:>`, `@@` or SetToBag), the
engine keeps the function lazy over the value, where it stopped with "a function over a non-set".
Applying one, or an EXCEPT of it, tests the key in the domain, which fails in TLC's
`TupleValue.member` and its siblings, as a FingerprintException where the value has a source: the
replay declines that failure where `CallStackTool` gave the domain one, a tuple or a record built
where it is written ("a failing test of a lazy function's domain that isn't a set"). A domain
built without a source, by Tail, Append, `\o`, SubSeq or an EXCEPT, or any domain in an
assumption, which `checkAssumptions` evaluates with the plain `Tool`, fails with the test's own
message, which the replay words, as `[e \in Tail(<<1, 2>>) |-> e][1]` ("Attempted to check set
membership in a tuple value."). Comparing such a function with a value that isn't a model value
fails in TLC (`FcnLambdaValue.equals` builds it): the store stops there with "a function over a
non-set", as the engine did building it, and the replay words the failure, as `1 = [e \in 1 + 1
|-> e]`. A startup definition whose value is such a function is evaluated again at each use, as
one that stopped building it, since the trace's evaluator can't take it as computed.
So does the engine where a bound's set is an expression whose value is never a set: an integer of
arithmetic, `Len` or `Cardinality`, a boolean of a comparison, a connective or a quantifier, a
sequence of Append, Tail or `\o`, an EXCEPT, or a model's constant whose value isn't a set, as
`[e \in mv |-> e]` or `[e \in (-2147483647 - 1) |-> e]` (6 runs of the upstream suite).
A domain that only evaluates to such a value otherwise, as a definition's name or DOMAIN of a
function kept lazy, still stops the engine.

A set enumeration of number, string and boolean literals of more than one kind, as `{1, "a"}`,
TLC holds as written, unnormalized, and normalizes only where an operation sorts it; the engine
can't hold one and stopped with "values TLC can't compare" wherever it was written. It now
computes, where the set is written there (not through a name or a parameter) and the other
operand has no effect, the operations that never normalize it:
- `S \cap T` and `S \ T` with the written set on either side, reduced as OPCODE_cap and
  OPCODE_setdiff reduce them (`SetEnumValue.cap` and `diff`): the elements of the Reducible
  operand the other holds or lacks, the written set's `member` searching its written elements
  with `equals` (`ValueVec.search`), as `({1, 2} \ {2}) \cap {1, "a"}` is `{1}`. Where the
  elements kept don't compare with each other, or the other operand is neither a set
  enumeration nor an interval TLC reduces by, or any test fails, it stops as before;
- `S \subseteq T` with T written so and S a set enumeration or an interval
  (`EnumerableValue.isSubsetEq`), TRUE for an empty S;
- `T \in S` with T written so and S an empty set enumeration or interval, FALSE
  (`ValueVec.search`, `IntervalValue.member`);
- `T = mv` and `mv = T` with an untyped model value, FALSE (`ModelValue.equals`,
  `modelValueEquals`);
- `IsFiniteSet(T)`, TRUE, and `IsABag(T)`, FALSE (`SetEnumValue.isFinite`, `Value.toFcnRcd`).
The trace evaluator's startup then found these computing where the search found them failing
("a startup definition the search found failing that computes", 19 runs of the value matrix).

The replay of a FingerprintException in `S \cap T` takes such a written S as the Reducible
receiver TLC calls (OPCODE_cap), whose `cap` asks T of each written element: S's source heads
T's. It took T as the receiver, which named the two sources in the other order, as in
`x' = Cardinality({1, "a"} \cap {x, 1})` from `x = 0` (wrong on main alike).

PrintT normalizes a copy of its argument before it prints it (`TLC.PrintT`, `deepNormalize`),
which for a set of functions or records TLC keeps lazy normalizes each of its sets in turn
(`SetOfFcnsValue.deepNormalize`, `SetOfRcdsValue.deepNormalize`), so `PrintT([{} -> {1, "a"}])`
fails to sort `{1, "a"}` though the empty domain spares it the printing. The trace evaluator
fails there too where the argument is such a set built of set enumerations of scalars, intervals
and such written sets, where it printed `{<<>>}` and the engine's failure then declined (4 runs
of the value matrix, in the assume context; the other contexts decline as before). Print, which
normalizes two values, is left as it was.

Still declined in that matrix: such a set as a factor of `\X` beside an empty set, which the
startup's confirmation of a comparison failure in a product leaves unsure,
`<<1>> \in Seq({1, "a"})`, and `\X`, `[S -> T]` and `[a : S]` of an empty set and a bag.

#### JSON files

`JsonDeserialize` and `ndJsonDeserialize` read a file as Gson 2.14, which TLC's jar bundles,
parses it (`JsonParser.parseReader`, lenient but for what follows the value), a port of its
`JsonReader` in `tla-values`'s `json.rs`: comments, unquoted and single-quoted strings, `;` and
`=>`, upper-case keywords, a missing array element as null, the `)]}'` prefix and a leading byte
order mark; an empty file is null. The engine stops at what TLC fails on, the failures TLC
reports: a file that isn't a string (`MethodValue`'s cast), one it can't open, JSON Gson rejects,
and null or a number `Integer.parseInt` doesn't read (`getValue`); and for `JsonSerialize` and
`ndJsonSerialize` a value `toTuple` (and `toRcd`) rejects, which comes before any other check of
the value, and a file it can't write. The replay words them: Gson's message with its line, column
and path, Java's `(No such file or directory)`-style message of the file's normalized path, and
`TLC_MODULE_ARGUMENT_ERROR`. It reads the file again only on the host's file system and where no
operator of the model writes files (`JsonSerialize`, `ndJsonSerialize`, IOUtils's `Serialize`,
`IOExec`), and words a write failure for a directory, and for a value `getNode` can't convert, as
`<<Nat>>` (`Cannot convert value: unsupported value type tlc2.value.impl.UserValue`): TLC makes the
file's directories and opens the file, emptying it, before it converts, and ndJsonSerialize's
`BufferedWriter` flushes the lines before the one that fails as it closes, so the replay does the
same to the file before it words the failure; where the conversion succeeds, or the file doesn't
open, it declines as before. `getNode` of a function TLC keeps lazy, or of Nat, Int or STRING,
which the store holds otherwise, stops the engine for the evaluator, which builds the function
(`FcnLambdaValue.toFcnRcd`), so `ToJson([x \in Nat |-> x])` fails counting Nat as TLC does, and
declines where it converts. It declines a read that succeeds, and
any of these failures in a model that prints, draws, sets a register or may warn of an EXCEPT:
TLC computes a constant definition that fails at startup again where it's used, repeating those
effects, and the front end doesn't count these operators among the definitions it computes at
startup. A text that starts with two byte order marks declines, as Gson's reading of the second
depends on how the file system splits the reads. Known wrong outside the suite, as in main:
`JsonSerialize` of the -metadir itself (a directory TLC makes before it evaluates, as the binary
doesn't) succeeds, where TLC fails with `(Is a directory)`.

Both operators read the file through a `FileReader`, whose `StreamDecoder` decodes it with the
default charset, UTF-8 on Java 21, and replaces each malformed sequence with one U+FFFD. Java's
decoder measures a malformed sequence otherwise than `String::from_utf8_lossy`: a UTF-8-encoded
surrogate (`ED A0 80`) is one malformed sequence of three bytes, and `ED` with a continuation byte
before a byte that doesn't continue is one of two, where Rust replaces each byte; a sequence the
file ends in the middle of is one. `tla_values::json::decode_file_text` ports
`sun.nio.cs.UTF_8.Decoder` and `CharsetDecoder.decode`'s end of input, and the engine and the
replay both read through it. It matched Java's `FileReader` on 200,000 random files (one in ten
past the 8,192-byte buffer, so a sequence is cut between reads), on every two-byte sequence, and
on 636,608 sequences of three and four bytes drawn from the bytes where UTF-8's ranges change. With `"\xED\xA0\x80"` (single- or
double-quoted) in the file, `Len(JsonDeserialize("data")) # (x + 1)` is a violated invariant on
TLC; the engine had read three characters and reported no error (`main` too, for the
double-quoted string). It finds the violation now and declines it while rebuilding the trace, as
it declines every read string outside ASCII there, as `main` does.

A Json operator writes its file through the run's journal (`tla_values::written`), so a run that
declines puts it back, `JsonSerialize` and `ndJsonSerialize` as IOUtils's `Serialize` (`main` left
the file `JsonSerialize` wrote).

#### Declines to win back

A correctness fix can turn a run that matched TLC into a decline, where the engine can't yet tell
it from one that printed something else. Each is outside the corpus:
- a constant definition with effects that converts a value with `ToJson`, `ToJsonArray` or
  `ToJsonObject` ("a constant definition with effects applying a Json operator, which TLC computes
  as it starts"), also where the conversion can't fail and nothing reads the definition more
  than once, as `Test == PrintT(ToJson(1))`, which an earlier build answered as TLC does and main
  declines (see the paragraph on Json operators TLC computes as it starts). Winning these back
  takes declining only where the conversion may fail as TLC starts or the definition is read
  more than once.
- a constant definition TLC computes as it starts whose `RandomSubset` or `RandomElement`
  operand prints other than as a Print or PrintT of arguments without effects, alone or as an
  element of a set enumeration of such prints and expressions without effects, or whose
  `RandomSetOfSubsets` operand prints, as `PrintT(RandomSubset(1, {Print(1, 1), 2} \cup {3}))`,
  `{Print(x, 1) : x \in {1, 2}}` or a definition naming such an enumeration ("unsupported:
  Print"). `Randomization.RandomSubset` and `RandomElement` are Java methods whose arguments TLC
  evaluates in order before it draws (`Tool.evalAppl`); the engine now compiles a print in that
  shape in the draw's order (`Compiler::is_eager_print_operand`), so `Test ==
  PrintT(RandomSubset(1, {Print(1, 1), 2}))` with `ASSUME Test` answers as main did, and its
  neighbours main is wrong on (a second `ASSUME Test`, `ASSUME PrintT("a")` before it, the
  definition unread) answer too (`random-subset-of-printing-enumeration*` fixtures). Main matched
  the shapes left only where the one assumption reads the definition once, after nothing else
  printed or drew: it evaluated the definition there, not in TLC's startup order. The trace
  evaluator now reports what a draw's normalization of the set throws as the Java method's
  failure (2154, `MethodValue.apply`), as `PrintT(RandomSubset(1, {TRUE, 2}))` fails in TLC,
  where it gave the comparison's message alone (`random-subset-of-unsortable-set`).
- a startup definition the search found failing whose failure the trace evaluator's startup
  can't place as one TLC raises (no TLC message: "values TLC can't compare" on a pair it doesn't
  word), as `Test ==
  PrintT([{1} -> {2, 3}] \subseteq ({1, 2} \cap {2, 3}))` with `ASSUME Test`, 108 runs of the
  guard-overreach set: the startup meets the pair with a function on the left, and only the
  replay at the use, with an integer on the left, words TLC's error. Only positive evidence
  confirms a swallowed failure, so it declines ("...that the evaluator can't follow"). To win
  them: hold an inconclusive confirmation pending, have the replays report which failed startup
  definitions they worded a failure through, and decline any outcome where one stayed pending.
- a failure whose call stack TLC heads with a source the replay doesn't place, outside an
  assumption, where TLC prints no frames (`UNFOLLOWED_FRAMES`): a comparison that fails as its
  message prints a set TLC holds unnormalized, which fails in that set's `normalize`
  (`SetEnumValue.toString`), as `Test == <<1>> = {"a", 1}` in Next ("a comparison that fails
  printing a set TLC holds unnormalized"); the membership in the set enumeration a function TLC
  keeps lazy holds as its domain (`FcnLambdaValue.apply`, `SetEnumValue.member`), as
  `[x \in {1, 2} |-> x]["a"]` ("the membership in the domain of a function TLC keeps lazy"),
  but of a number, a string or a boolean in the set a definition of constant level names, which
  TLC computed as it started with its plain `Tool` and keeps without a source, as `S == {"b",
  "a"}` with `[x \in S |-> x][1]` (TLC reports the failure with the application's frames, and
  `CallStackTool` applies a copy of the FcnLambdaValue without a source); and
  the search of a function of one key whose argument the call stack didn't keep ("a function's
  search of its keys whose frames the call stack doesn't place": an argument it didn't keep, or
  a key that isn't an integer, a boolean or a string, which may have a source). Under `ASSUME` each answers: TLC tests a
  union of set enumerations and intervals in the set it builds unnormalized (`Reducible.cup`),
  a function of one key in the `equals` of its key (`FcnRcdValue.selectLinearSearch`), a lazy
  function in its domain's elements as written, and a comparison's message prints its operands
  as `toString` does, failing where a set enumeration it prints fails to normalize. A failed
  startup definition no longer declines as one holding a product or a power set (or a set map)
  where its failure is a comparison the evaluator follows as TLC makes it: an integer's, a
  string's, a boolean's or a function's `equals` given a lazy set whose text is known, which it
  reads only to print, as `(1 :> 2)[{1, 2} \X {3}]` or `<<1>> = SUBSET {1, 2}`, or
  `PrintT(S \cup T)` of a set of scalars S (or of sets of scalars, or the power set of a set of
  scalars) and a set of tuples, records or functions T of such sets, whose
  `SetCupValue.toString` sorts S's elements and then fails on T's first (`is_known_cup_print`).
  A scalar's failed comparison with a lazy set whose parts hold a set enumeration TLC can't
  normalize declines ("equality of values TLC can't compare"), as `1 = {"a", 1} \X {1}` or
  `1 = SUBSET {{1, "a"}, {2}}`, where it printed the set's operation before and TLC fails as
  `toString` normalizes the parts. A set enumeration or an interval compared with a set
  enumeration TLC holds unnormalized fails as that set's `normalize` does
  (`SetEnumValue.compareTo` and `equals` normalize the argument before either prints), as the
  sort of `{{1, "a"}, {2}}` does printing `<<1>> = {{1, "a"}, {2}}`; a lazy set compared so
  declines.
  A function of several arguments TLC keeps lazy, written in place, of at most one key and a
  body without effects, applied to a value that is no function, fails as `FcnLambdaValue.apply`
  words it ("the argument list is: ... which does not match its formal parameter"); outside an
  assumption, where TLC reports it with where the function was built, it declines ("the
  argument list of a function TLC keeps lazy").
  `r.f` of a function that isn't a record searches its keys for the field one by one, as
  `FcnRcdValue.select` does a function TLC built and sorted below 32 keys, or one it builds of a
  lazy function over a set enumeration (`toFcnRcd`), where every key is an integer, a boolean or
  a string, as `[x \in {1, 2} |-> x * 2].a`; an EXCEPT's `Value.select` (`Tool`'s OPCODE_exc)
  searches a sorted function so too, as `[(3 :> -1) EXCEPT !.a = 1]`.
- a startup print that may hold a set of tuples, records or functions TLC fails to size, as the
  compiler reads it from the text (`may_write_unsized`), where TLC prints it: a set nested in
  another value whose parts the compiler can't prove sized as written (`is_sized`: enumerations,
  intervals, BOOLEAN, written domains and LET bodies, and sets built of those), as `Id(S) == S`
  and `Test == PrintT(<<{1} \X Id({2})>>)`; or such a set as the argument of a user operator
  whose body discards it, as `Ignore(S) == 1` and `Test == PrintT(Ignore(Int \X {}))`, since every
  argument of an operator counts as carried; or such a set a set map's or a filter's bound
  ranges over where the mapped or filtered expression's result doesn't hold the name, as
  `Test == PrintT({1 : x \in {Int \X {}}})`; or any argument of a recursive operator re-entered
  in its own walk. Main printed each, and the engine can't yet tell it
  from a print TLC fails to size, such as `<<{1} \X Id(Int)>>` or `Id(Int \X {})`, so the startup
  definition declines ("a set TLC may fail to print, at startup"). Telling them apart needs each
  part's size and kind (a non-set part fails in TLC too) where the set is built, and whether its
  value reaches the print, through every binding of an argument or a LET.
- a configuration error in what the configuration names for the search (CONSTRAINT,
  ACTION_CONSTRAINT and the like), where a constant definition prints: TLC prints what the
  constant definitions print first (`processConstantDefns`), which the front end, raising the
  error as it reads the configuration, doesn't; it declines it ("what the spec prints as TLC
  computes its constants", as the library's check does), which main answered without the prints.
- a startup definition that failed, used in the initial predicate or a step, that fails there in
  a method of a value with a source or of an interval, which the replay holds without one: TLC
  reports the failure as a state it fails to fingerprint (see the known wrong output below); the
  trace evaluator declines it, and a variable `x = D` assigns where it can't word D's failure.
- a union TLC fails to enumerate at once (`UnionValue.elements`: of a value that isn't
  `Enumerable`, whose message names the Enumerator's own `Object.toString`, or whose first set
  isn't), met in a state or a step, where the replay can't tell which values' sources TLC's
  FingerprintException passes through: it follows the union as the set of a CHOOSE, a
  quantifier, a set filter or a set map, as `Cardinality`'s argument, and as the only such union
  given to or held one level down in the value whose method failed with a source, and otherwise
  declines ("a union of a value that isn't a set, enumerated by another value"). It declines too
  where an operator returned the union itself, which TLC's `setSource` gives that operator's
  source (`{} \cup S` and `(1..0) \cup S` by `SetEnumValue.cup` and `IntervalValue.cup`, DOMAIN
  of `[x \in S |-> e]` by `FcnLambdaValue.getDomain`): "a union of a value that isn't a set,
  given a source again by an operator returning it". An initial state holding a filter of such
  a union (`{x \in UNION 1 : TRUE}`) fails in the union's method, which TLC reports as an
  exception it didn't expect: the fingerprint declines it ("a state whose fingerprint the replay
  doesn't follow"). In an assumption or a startup definition no value has a source, and the
  message alone is TLC's.
- SUBSET of a value that isn't a set, which TLC holds lazy (`SubsetValue`) and fails where a
  method of it asks its base's size or enumeration: the trace evaluator follows it only as
  PrintT's own argument as TLC starts (an assumption or a startup definition), where TLC's
  `toString` asks the base's `size` (failing for a value of no keys), then expands a base of
  fewer than 7 keys (`{{}}` of none, else `elementsNormalized`'s non-enumerable failure). A base
  of 7 keys or more, which TLC prints as written, a function TLC keeps lazy, and every other use
  still decline ("SUBSET of a non-set"); so does a base of no keys where the search found the
  startup definition failing.
- a startup definition that failed, evaluated again where it is used, whose evaluation held a
  set enumeration TLC can't normalize, or a value TLC may hold lazy, and failed otherwise than in
  normalizing it ("a startup definition that failed where TLC may fail otherwise"): TLC, which
  normalizes such a set where the evaluator may not, may fail elsewhere. One exception is the
  only such set the evaluation built, written as the operand of `~`, `=>`, `<=>` or DOMAIN that
  fails on its kind, as `PrintT(~{1, "a"})`, whose failure TLC raises before anything normalizes
  it and words with the set's kind alone; the others are the failures, in an assumption, whose
  message prints no such set (`unsorted_prints`, under "A failed startup assumption evaluated
  again that built a set TLC can't normalize" above), and, in an assumption, a failure in the
  body of a function TLC builds as it meets it (a single name over a set enumeration or an
  interval). Outside an assumption all of these still decline.
- `[x \in S |-> e][a]` as TLC starts, with the constructor written in place, which TLC keeps
  lazy (`EvalControl.KeepLazy`) and applies without building (`FcnLambdaValue.apply`), where the
  evaluator, building it, fails in `e` at another key ("the body of a function TLC keeps lazy, at
  a key it may not evaluate"): where neither the constructor nor `a` may have an effect and S is
  a set enumeration or an interval, the evaluator applies it as TLC does instead, `e` at `a` in
  S, and otherwise TLC's message with the function built, or, where a key's body fails, unbuilt.
  So too for a constructor of several bounds of one name each, `[x \in S, y \in T |-> e][a]`,
  where the evaluator, building it or testing `a` against its domain, declines: TLC converts `a`
  to a tuple (`toTuple`), words a value that isn't one, tests its parts in order against the
  domains, fails on a missing part as Java's array does (`Index 1 out of bounds for length 1`),
  and ignores extra parts. Where a value of the body holds a set TLC can't normalize, or one
  whose text the evaluator doesn't know, TLC's `toString` swallows its failure into another text,
  and the evaluator declines (`[x \in {1}, y \in {2} |-> {"a", 1}][1]`). Any other shape, a
  LET's name for the constructor or a tuple or grouped bound included, still declines.
- a SYMMETRY definition with parameters, whose body TLC evaluates without them
  (`Tool.getSymmetryPerms`), failing at the first parameter it reads or going on with the value.
  The front end reported that it isn't a set of permutations, which TLC never prints for one; it
  declines it (`a SYMMETRY definition with parameters`).
- a tuple binder over a set containing a tuple before an equal function, such as
  `{<<1,2>>, [i \in 1..2 |-> i]}`: TLC retains the tuple and succeeds; the engine's shared
  value mark can also represent the function, so replay finds no failure and the run declines.
- a tuple binder replayed over a function whose concrete TLC class was lost during transfer:
  the trace evaluator declines because a tuple-shaped function may be a `TupleValue` or a
  `FcnRcdValue`, which `ContextEnumerator` treats differently. Direct tuples and functions
  with retained class provenance are checked using TLC's class, and reducible filters report
  the corresponding Java cast failure.
- a function constructor that binds a tuple pattern over a set of functions TLC built as
  functions, applied at once (`[<<a, b>> \in {[k \in 1..2 |-> k]} |-> a][<<1, 2>>]`). TLC applies
  the function without building it, so it never binds the pattern; the engine builds it and
  declines the binding, since `ContextEnumerator` binds a tuple pattern only to a `TupleValue`
  (#245).
- a lazy set streamed where TLC may have normalized the object it streams, whose stream differs
  from the normalized set only where nothing printed depends on it (`lazy-duplicates.md`): an
  invariant violated before the stream first differs, or a stream whose order alone differs
  where the first initial state to violate an invariant is the same in either order. Nine cells
  of `prove-it-cli/tests/lazy_duplicates.rs` printed what TLC prints so before and decline now:
  `kept.cupOrder.{constVar, ex1, letEval, opAfter, varPlain}.init` and
  `kept.unionSub.{constHeld, constSized, constEqual, constCup}`. To win them back, decline at the
  first position where the stream differs from the normalized set, not where the stream starts.
- `TLC!RandomElement` where a failure needs the generator after a failed startup draw, or
  a physical set/function class the evaluator does not retain. Direct Print operands and printed
  tuples of direct draws now use the shared Java generator in TLC's order. The default Java
  method has level zero and is impure. The new printed-draw and diagnostic paths, as well as
  the level correction, require closed default-method origin metadata; unproved legacy methods
  retain their earlier mathematical path and unsupported errors. Configured operator tables
  use their rows rather than authorizing the default random algorithm.
  A non-set argument fails before any draw, and a function/record/product's first component may
  be checked before acquiring the generator where all preceding normalization is known. The
  no-draw diagnostic keeps TLC's default value formatting. Empty enumerations and intervals
  consume one double before failing; they remain declined where the legacy startup/replay path
  cannot retain that failed draw, rather than replaying with a substitute seed.
- a file of the user's named Naturals, Integers, Sequences, FiniteSets or TLC replaces the
  standard module (`SimpleFilenameToStream.locate`), and TLC binds its jar's Java class to the
  file's definitions by name alone (`processModuleOverrides`), whatever their bodies. The front
  end links the file and keys each definition the standard module also defines, with its arity,
  as the standard builtin, under the key the jar's module gives it (`PrintT`, not the file's own
  key), so that every check of what a definition reaches, such as a print at startup, sees the
  builtin as it does with the jar's module. A Java method the file defines with another arity, or that the
  standard module doesn't define (Sequences' `Cons`, `Insert`, `SelectInSeq`), is a declined
  builtin, which declines where the spec evaluates it (TLC fails there as the method's arity
  demands, or evaluates the method). A standard module TLC's jar holds that uses a replaced one
  declines (`a standard module that uses a module a file of the user's replaces`), as Bags or
  Json with the user's Naturals, but where the file's text is the jar's own module, byte for
  byte, which defines what the jar's module does (Json beside a copy of TLC.tla, Bags beside one
  of Naturals.tla), and but TLC, Sequences, FiniteSets and Randomization: every operator of
  theirs is a Java method (`TLC.java`, `TLCGetSet.java`, `TLCEval.java`, `Sequences.java`,
  `FiniteSets.java`, `Randomization.java`) whatever the file's definitions their bodies would
  use, but Randomization's TestRandomSetOfSubsets, whose body names only Java methods, which TLC
  binds to the file's definitions by name. TLC doesn't check the assumptions of a file only such a
  module's LOCAL INSTANCE reaches (`user-sequences-tlc-local-instance`: a user Sequences.tla
  holding `ASSUME FALSE` beside `EXTENDS TLC, Naturals` exits 0), checks those of one the spec
  extends (`user-sequences-tlc-extended`, where main prints "No error has been found"), and SANY
  reads the file as the front end does (a user Sequences without Len fails SANY under TLC.tla).
  main matches the other declined shapes only because it never reads such a file: with the
  user's Naturals.tla holding `ASSUME 1 + 1 = 3`, `EXTENDS Naturals, Bags` makes TLC report the
  assumption false, where main prints "No error has been found"; without the ASSUME, both print
  TLC's output. TLCExt, whose operators TLA+ defines in part (TLCGetAndSet, AssertEq), uses only
  TLC and Integers (`LOCAL INSTANCE`), so beside a user's Sequences or FiniteSets, which only
  TLC's Java methods reach, it answers as TLC does (a user Sequences.tla holding `ASSUME FALSE`
  beside `EXTENDS TLCExt, TLC` exits 0); beside a user's TLC, Integers or Naturals it still
  declines. The trace modules TLC adds where it writes its trace exploration spec (`_TLCTrace`,
  its default without -noGenerateSpecTE, and the -dumpTrace modules) instance TLC and TLCExt,
  which the linking doesn't follow: TLC computes a constant definition again for each module
  whose definitions hold it, so `Foo == PrintT("hidden")` added to a user's TLC.tla beside
  `EXTENDS Integers, TLC` prints three times (twice for a user's Integers.tla), once with
  -noGenerateSpecTE. The binary printed it once and main never; a definition that prints or
  draws such a file adds declines there ("a definition with effects that TLC computes again for
  its trace modules, in a file of the user's that replaces TLC"), TLCExt's as well (`EXTENDS
  Naturals, TLCExt` beside a user's TLCExt.tla with that `Foo` prints it twice). The trace
  modules read such a file whether or not the spec names it: beside `EXTENDS Naturals` alone the
  same `Foo` in a user's TLC.tla prints three times, in a user's Integers.tla (with `LOCAL
  INSTANCE TLC`) twice, through TLCExt's `LOCAL INSTANCE Integers`, where the binary and main
  printed it never. The front end links each file of the user's the trace modules read (TLC,
  TLCExt, Sequences, Naturals, Integers, FiniteSets, and Json for `_JsonTrace`) on its own, and
  declines where it or a file of the user's it reads holds such a definition ("..., in a file of
  the user's they read, TLC"); a file that fails to link on its own declines nothing more. A
  register such a definition sets TLC sets on no checker as it starts (`TLCGetSet.TLCSet` fails
  without a `mainChecker`, and `processConstantDefns` swallows it), so `Foo == TLCSet(1, 5)`
  shows nothing however often TLC computes it, and answers. main matches a declined definition
  whose evaluation shows nothing, only because it never evaluates it: `Foo == IF FALSE THEN
  PrintT("hidden") ELSE 1` prints nothing in TLC either, but with `IF TRUE` TLC prints three
  times where main prints never.
- an operator of a module of the user's named after a class TLC counts as its own
  (`BuiltInModuleHelper`: TransitiveClosure, Randomization, AnySet, Bags, Json, TLCExt, ...),
  which TLC replaces by the class's method whatever the module's text (`processModuleOverrides`).
  Unsupported overrides reached from a definition, assumption, INSTANCE substitution or model
  configuration decline (`an operator of a module of the user's that TLC's Java class replaces`).
  A user module's one-argument `TransitiveClosure!Warshall` is implemented for any relation
  whose expression can't print, draw or set a register (with an operator parameter declining): TLC
  enumerates the relation, converts each element to a tuple and fingerprints its endpoints, which
  may force a function it keeps lazy. The engine stops at an element that isn't a pair, for the
  evaluator of failures to word TLC's first in TLC's order; it declines an element that is a
  function TLC keeps lazy, or an endpoint TLC may fail to fingerprint. TLC returns an initially
  unnormalized enumeration; replay retains its order until TLC normalizes it. Other arities
  decline. The trace evaluator follows `Warshall` twice over (`warshall_enumerated`,
  `warshall_followed`), answering where either answers and declining where both answer and
  disagree ("Warshall of a relation the two walks disagree on"). The first words the failures for
  a set enumeration (normalizing it inside the method, whose comparison failure TLC wraps as the
  method's, where every element is held as TLC holds it), an interval, a power set of a set
  enumeration (whose first subset `{}` fails), and a plain scalar, function or Nat, Int or STRING
  that isn't `Enumerable`. The second follows any set enumeration, interval, power set of fewer
  than 31 elements or product of those: a value that isn't `Enumerable` (Nat, Int, a non-set)
  fails with 2176, an element `toTuple` doesn't make a pair with 2157, and a set it can't
  normalize as the method's failure; it finds endpoints as the method's Hashtable of fingerprints
  does, comparing only values of one kind. Endpoints neither can compare, other lazy sets (filters
  and unions it keeps lazy) and lazy elements decline. A user-provided Java class takes precedence and follows the
  existing Java override handling. A declared three-argument `Randomization!RandomSubsetSet`
  uses the pinned Java coin-toss algorithm: exactly one JavaRandom double per base element per
  requested pick, including probabilities zero, one and NaN, with duplicate subsets discarded.
  Probability strings follow Java Double syntax, including hexadecimal literals. The binding
  requires closed Java-origin metadata proving the default class applies; the shipped module
  still does not declare this operator. Concrete finite enumerations and intervals preserve
  shared-value normalization when Java fingerprints each selected subset. Deferred set/function
  normalization and effects in a function TLC keeps lazy remain declined: their hash-time cache
  and effect order are not yet tracked. Startup evaluation retains the Java method's level-zero,
  impure draw lifecycle. `RandomSetOfSubsets(k, n, S)` uses the same coin-toss algorithm with
  probability `n / Cardinality(S)`, including NaN for an empty base and zero average. It checks
  the requested-pick capacity before the average-size range, and keeps the same concrete-value,
  lazy-normalization proof boundaries. Its default Java method now requires positive closed
  class and override-index metadata even on a legacy metadata path; an indexed replacement
  cannot acquire authority merely from the operator's name. Unknown methods decline only where
  evaluated. Configured operator tables retain their table semantics. Cardinality of a direct
  draw may be
  printed or compared with an integer literal where the engine evaluates that draw once.
  Packaged `AnySet!ANY` and TLC Any use the value capability described above.
- a configuration substitute `C <- D`, and an operator a TLCOverrides index replaces, where TLC
  computes the definition or the Java method again at each read: TLC holds C as D's definition, so
  it prints, draws and sets registers again wherever it reads C, and calls a `final` method without
  parameters as it loads it (`MethodValue.get`). Native runs keep main's behaviour for the
  substitute, which matches only where nothing after the read shows the difference, and prints
  other output where something does; an operator the index replaces now declines where the
  model evaluates it, and a `final` method without parameters always (see "Java overrides that
  stay declined"). The groups: register readers, TLCGet("level") printers, invisible override reads, random
  draws, final methods, VIEW and POSTCONDITION reads, and recursive-operator arguments. The
  `front-constants-full` branch declines them where the run computes the read
  (`Definition::READ_DECLINED`) and reads the index. Its 13,067 adversarial specs, against TLC at
  d8fb231, on the `front-constants-cases` branch, are the regression set for winning them back.
  Where a substitute reaches AssertEq, TLCGetOrDefault, TLCGetAndSet or PickSuccessor, where a
  constant definition reads TLCExt's registers, or where only PickSuccessor makes
  a constant definition impure, the IR marks the four `Builtin::DECLINED`, and the engine declines
  them where it computes them, as it did before it checked them. A constant definition that reads
  them isn't declined where TLC and the engine both compute it as TLC starts (TLCGetOrDefault has
  no minimum level, so the front end counts it constant, and TLC reads no register then), nor
  where it reaches TLCGet, whose minimum level keeps TLC from computing it before its uses. An
  assumption that reads them no longer marks them: TLC checks the assumptions once its checker
  exists (`AbstractChecker.checkAssumptions`), from its main thread, where TLCSet of a number sets
  every worker's register (`setAllValues`) and TLCGetOrDefault reads worker 0's, as the engine
  checks them, and the search reads what they set; a constant definition the assumption names
  is still computed as TLC starts first.
- an action constraint that applies a constant function outside its domain
  (`f == [i \in 0..2 |-> i]`, `AC == f[x'] > 0`, the failDom* cases of
  `prove-it-cli/tests/action-constraint-failures`). TLC words the failure with the `FcnRcdValue` it
  computed as it started (`Attempted to apply function:`), which the evaluator doesn't build, so
  the binary declines it (`applied a function outside its domain`), as it did before action
  constraint failures were native. To win them back, build a constant definition's function as
  TLC computed it at startup.
- a subscript of `[][Next]_v` that an operator leads back to itself, such as `RECURSIVE F(_)`,
  `F(n) == F(n)`, `[][x' = x]_<<x, F(0)>>`, or a definition without parameters that names itself,
  `F == F`, directly, mutually, or through a LET, an operator argument, an INSTANCE or a constant
  the configuration substitutes. TLC's SubscriptCollector enters the operator's body again and again
  until its stack overflows, and prints the StackOverflowError (exit 255), whatever -nowarning
  says; the front end read it without end and aborted the process, or on main took no subscript
  warning from it and checked the model. It declines where its reading nests deeper than 256,
  far deeper than a subscript's operators nest (`a subscript of [][Next]_v that an operator leads
  back to itself`). To win them back, prove the reading doesn't end, as for a cycle of operators
  that names no parameter, and print TLC's StackOverflowError.
- a subscript of `[][Next]_v` the subscript collector can't follow, which declines where TLC may
  print its warnings, unless -nowarning, and is read as TLC reads it otherwise. Main printed no
  warning for any subscript, so each matched where TLC prints none. What the collector still
  doesn't follow (`spec.rs`, `Unfollowed`):
  - a builtin passed as an operator argument, `Ap2(F(_, _)) == F(<<x>>, <<y>>)` with
    `[][...]_(Ap2(\o))`: TLC reads one its Java method replaces, `\o`, as a value it ignores
    and warns that the subscript holds neither variable, and one it doesn't, `\cup`, as a node
    without a body, failing to read it (could not determine); main printed neither warning.
  - a substitute applied with other than its own arguments, which TLC's configuration rejects
    before (`CONSTANT C <- G` with `G(a)`: "substitutes for C with G of different number of
    arguments"), so no run reaches it.
  - a subexpression name, a name the front end doesn't follow, and a definition TLC may compute
    as it starts that the front end neither computes nor reads to the end: none of 470 probes of
    the subscript (`scratch/upstream/fuzz/subscript-position` on `upstream-results`) reaches
    them, the front end resolving subexpression names and INSTANCE copies before.
  To win them back, tell a builtin TLC replaces by a Java method from one it doesn't.
- SANY's report of a spec that extends a module of the CommunityModules (`EXTENDS SequencesExt`)
  that no file beside the spec holds. The TypeScript report printed that SANY can't find it,
  which TLC prints only where CommunityModules.jar isn't beside tla2tools.jar: it matched TLC by
  where the jar was. The report declines it, as the binary did; winning it back takes knowing
  whether TLC's class path holds the CommunityModules.
- a write of a value once the run has enumerated a set of functions, records or tuples that TLC
  keeps lazy and prints by its parts: one with a part TLC can't size before an empty one, such as
  `[a : Int, b : {}]` (`SetOfRcdsValue.toString` sizes the parts in order). TLC compares,
  fingerprints, sizes and enumerates such a set as its enumeration, which decides emptiness before
  it asks a part, so the engine holds it as that enumeration, `{}` or `{<<>>}`, and a trace's
  states, which the trace evaluator prints, and a failure it explains print it as TLC does. Only
  what the engine writes itself would print the enumeration instead: Print, PrintT, AssertEq and
  ToString of a value that may hold such a set (`may_write_held`), `-dump`, a simulation's trace
  and the message of a constant conjunct of the specification. These decline (`writing a value
  that may hold a set TLC prints by its parts`, `dumping a state that may hold a set TLC prints by
  its parts`). The engine records such an enumeration for the run (`Program::holds_collapsed`), not
  for the value, so a write of a value that holds none declines too, where main printed it as TLC
  does. Of 1,600 adversarial specs against TLC (four seeds of `scratch/upstream/gen_lazy.py` on
  the `upstream-results` branch), none matched on main and declines. To win them back, keep the
  lazy set as a value the store holds and prints as TLC does.

A property's \A that TLC unrolls, or takes whole, with the substitutions of the INSTANCEs it went
through left unbound declines where it is a tautology or has a constant part that isn't a boolean,
as on main. Branch `live-stops-full` follows TLC's lookup there: lazy operator arguments, LET
definitions and closures read in the context they are written in, a definition named from outside
its INSTANCE entered through its own `SubstInNode`, and root constants and configuration overrides
read past an INSTANCE. Eight adversarial rounds kept finding edges in it (nested INSTANCEs that
substitute a bare name, operator arguments naming an INSTANCE's copy), so it waits there.

An imported assumption or theorem can refer to a WITH numeral or string whose semantic Expr
object `SpecProcessor.processConstants` never initialized. The lowering retains that literal's
identity: an ordinary copied definition can initialize the shared Expr, while a separate literal
with the same value does not. The native engine defers an unavailable literal; replay reports
primitive equality's NullPointerException with its operand order and effects intact. A top-level
null result stays a lazy-argument cache miss while replacing the previous cache entry; a non-null
container holding null still caches normally. Other null
consumers and state-dependent replays whose failure phase is unproved still decline. Structural
sequence operations and cardinality preserve null members they do not inspect. Startup inspection
of an operator constant bound to a core built-in follows `getLevelBound` through the configured
receiver key; preceding effects or unverified TLC versions remain declines. The `instance-null-*`
fixtures record these cases and initialized aliases against the pinned Jar.

A quantifier's or a set map's bound that is an interval of more than 2^31 - 1 elements fails as
TLC counts it: `Tool.contexts` enumerates each bound in normalized order, which an interval gives
by building its elements after counting them (`EnumerableValue.elements(Ordering)`, `toSetEnum`,
`IntervalValue.size`), so `\E x \in MinInt..MaxInt : x = 0`, `\A`, `{x : x \in 0..MaxInt}` and a
bound after an empty one report `Size of interval value exceeds the maximum representable size
(32bits)`, in every context, as the corpus's `ValueSemanticsAssume.cfg` (`AssertError` of it)
expects; an interval up to 2^31 - 1 elements too large to build, which TLC builds, still declines.
CHOOSE enumerates its set the same way (`OPCODE_bc`, `elements(Ordering.NORMALIZED)`), so
`CHOOSE x \in 0..2147483647 : x = 0`, alone, LET-named, with a tuple pattern or within a
quantifier, reports the interval's size in every context, as main did in an assumption, where it
declined ("an interval too large to build"); `1..2147483647`, which TLC builds and runs out of
memory on, still declines (22 shapes, 110 runs: 85 match, 25 decline, none wrong).
A bound that is a set of functions, records or tuples with such an interval as a part fails the
same way, before the bound of `TLCGlobals.setBound` can: `toSetEnum` makes the Enumerator first,
whose `elements` asks whether the set is empty (`Value.isEmpty`), which counts each part in turn
up to an empty one, so `\E <<a, b>> \in (0..2147483647) \X {1} : TRUE`, `[a : 0..2147483647]`,
`[{1} -> 0..2147483647]`, a nested product, CHOOSE, a set map, and a union, `\cup` or `\` that
starts such a set report the interval's size, where they reported the set bound (`Attempted to
construct a set with too many elements`); `(0..2147483647) \X {}` reports it too, since the
interval is asked first. In the initial predicate, a step or a check, the FingerprintException
holds the sources of the sets whose `isEmpty` and `elements` it passes through, which the replay
places for a set of functions, records or tuples, nested ones, a `\cup` or `\` that starts one,
and the UNION of one; where a filter or a later set of a union holds it, it declines ("an interval
TLC fails to count within a bound the evaluator doesn't place", or "a union TLC counts an interval
within past its first set"). Main declined these outside `ASSUME`; 320 probes in five contexts
answer 263 and decline 57 with none wrong, and none main matched declines but
`[(0..2147483647) \X {1} |-> 1] = <<>>` under `ASSUME`, which declined before
("built a function over an infinite set").

An assumption that enumerates an interval of more than 2^31 - 1 elements where TLC walks it
without counting it (`IntervalValue.elements`), such as `(0..2147483647) \subseteq {0}`,
`(0..2147483647) \subseteq Nat`, `(0..2147483647) \in SUBSET {1}` or
`{x \in 0..2147483647 : TRUE} \subseteq {}`, no longer reports `Size of interval value exceeds
the maximum representable size (32bits)`: the evaluator's enumeration of the interval no longer
counts it, and declines ("an interval too large to build"), as it does in the other contexts,
where the search stops at the interval (probed against the jar on integration, 2026-11-18).

Outside the corpus, a correctness fix declines where main printed other than TLC:

- a constant definition TLC computes as it starts (`processConstantDefns`) that reaches TLCSet
  or AssertError, whose Java methods have no minimum level, where the front end counts both
  state-level and the engine computes the definition at each use instead. TLC computes it before
  `TLC.java` makes the checker, so TLCSet of a number throws there (no checker or simulator to
  set), as does a key it doesn't take, and TLC computes the definition again at each use after
  showing what ran before; TLCSet of a named register, "exit" or "pause" sets nothing and TLC
  keeps the value. Main printed these other than TLC: `D == PrintT(1) /\ TLCSet(3, 5)` printed
  `1` once where TLC prints it twice, `D == TLCSet("s:a", 5)` with `Test == D /\ TLCGet("s:a") =
  5` passed where TLC fails on the register it never set, `D == TLCSet("pause", FALSE) /\
  PrintT(2)` read twice printed `2` twice where TLC prints it once, and an unread `D == PrintT(1)
  /\ TLCSet(1, 0)` printed nothing. The front end declines such a definition ("a constant
  definition TLC computes as it starts that sets a register") but where TLCSet of a literal key
  TLC fails on and a value without effects comes first, before any effect, as the first operand
  of a conjunction or a disjunction, the left side of an equality, an implication or an
  equivalence, the operand of a negation (`~TLCSet(0, 42)`), or through a definition named
  without arguments (`fails_first_at_startup`), where the definition has no effect but through
  such definitions (`reaches_effect_past_failing_first`, as `Test == D /\ D` or `\A i \in {} :
  D`), or where TLCSet of "exit" or "pause" and a literal other than TRUE sets nothing and nothing
  else shows. It answers too a definition that sets nothing as TLC starts
  (`sets_nothing_at_startup`): one built, by operators without effects of their own, of parts
  that each fail first or have no effect, with a junction's operands without effect before one
  that fails first whatever they evaluate to (`(1 \div 0 = 1) /\ TLCSet(1, 2)`, `FALSE /\
  TLCSet(1, 2)`, `TRUE /\ TLCSet(1, 2)`, `Assert(FALSE, "m") /\ TLCSet(1, 2)`, `(1 = "a") /\
  TLCSet(1, 2)`), a quantifier or CHOOSE over sets built without effect whose body sets nothing
  for any element (`\E v \in {1, 2} : (v = 2) /\ TLCSet(1, v)`), a LET whose definitions have
  no effect, an operator whose body sets nothing whatever its arguments, and parts the constant
  evaluator computes as TLC does: a tuple's or a set enumeration's elements, an equality's or a
  membership's sides, a junction's operands up to one that decides it, and an IF's condition
  and the branch it takes (`IF \E v \in {} : TLCSet(1, 2) THEN PrintT(1) ELSE TLCSet(2, 3)`).
  TLC fails there before any effect, which `processConstantDefns` swallows, or keeps a value it
  computed without any, which the engine computes alike at each use. A definition nothing reads
  with another effect TLC shows as it starts, whose TLCSet sits in a branch the evaluator finds
  TLC doesn't take (`D == PrintT(0) /\ FALSE /\ TLCSet("-Dbar", 3)`), declines too ("a constant
  definition TLC computes as it starts with effects and TLCSet only in a branch it doesn't
  take"): TLC prints 0 as it starts, where main and the engine, computing no unread
  definition, print nothing (`unread-print-pruned-property-set`); one whose effect TLC doesn't
  reach either, after a part that decides the whole (`(1 = 1) \/ (PrintT("x") /\ TLCSet(1,
  2))`, `FALSE /\ PrintT("x") /\ ...`, an IF's branch not taken, `\E x \in {} : PrintT(x) /\
  ...`), answers. A root definition without other effects that the constant evaluator,
  computing TLCSet and Assert as TLC does as it starts, computes without reaching TLCSet or
  fails on answers too: TLC's TLCSet of a numbered register fails there whatever the key's
  expression (`S(k) == TLCSet(k, 2)` with `D == (1 = 1) /\ S(1)`, `TLCSet(CHOOSE i \in {1} :
  TRUE, 2)`, `\A x \in {1, 2} : TLCSet(x, 2)`, `LET k == 1 IN TLCSet(k, 2)`, `TLCSet(1 + 0,
  2)`), and the failure, before which nothing was set, makes TLC compute the definition at each
  use, as the engine does. The static rules also follow TLC's order of evaluation through the
  arguments of the builtins it evaluates in order before it applies them (`\cup`, `DOMAIN`,
  `SUBSET`, arithmetic, `Len`, `:>` and the rest, `EAGER_BUILTINS`), through a function
  application, which evaluates the function and then the argument and fails on a function that
  is a number, a string, a boolean or a set (`(TLCSet(1, 2))[1]`, `(SUBSET {1})[1] = PrintT(2)`,
  `(TLCSet("s:a", 2))[1]`, as TLCSet of a named register, "exit" or "pause" gives TRUE as TLC
  starts, setting nothing), and applies a constructor it keeps lazy at the argument, whose body
  then fails first (`[i \in {1, 2} |-> TLCSet(1, i)][1]`), through a filter's set, a membership
  in an interval that isn't empty of a value that is no integer (`{} \in 1..2`, `<<1>> \in
  1..2`), a LET whose body evaluates one of its definitions first
  (`LET L == TLCSet(1, "a") IN <<L, L>>`), and a function constructor TLC builds at once
  (OPCODE_fc's `toFcnRcd`: over set enumerations and intervals that aren't empty, where no
  application keeps it lazy, the body first at the domain's first element), so that
  `TLCSet(1, TLCSet(1, 2)) \cup Print(...)`, `DOMAIN TLCSet(1, [x \in {"a"} |-> 1])` and
  `PrintT({x \in [i \in 1..2 |-> TLCSet(0, i)] : TRUE})` answer (`tlcset-operand-fails-first`,
  `tlcset-function-built-at-startup`). Where the front end can't tell, the engine computes the
  definition as TLC starts, after the definitions it computes there, stopping at its TLCSet:
  where that is of a number or of a string TLC doesn't take for a key, and nothing printed, drew
  or warned before, or where the definition failed before any effect at a failure TLC reports,
  or completed without one, and without passing a TLCSet of a named register, "exit" or "pause",
  which sets nothing there and gives TRUE, to a boolean, a number or a string, TLC computes the
  definition at each use or keeps a value the engine computes alike, and the model answers
  (`tla_ir::Startup::register_probes`, `probe_registers`); anything else declines there ("the
  engine declined: unsupported: a constant definition TLC computes as it starts that sets a
  register", `tlcset-taken-print-at-startup`). So a part TLC fails on first that the front end's
  evaluator doesn't compute (`<<>> = {}`, `"a" < "b"`, `Len({}) = 0`, `1 % 0 = 1`, `<<1>>[0] = 1`,
  `IF 1 THEN TRUE ELSE FALSE`, `\E v \in [(1..2 \cup {<<1>>}) -> {}] : TLCSet(2, 1)` as an IF's
  condition), or that decides a junction first (`(Len(<<1>>) = 1) \/ (PrintT("x") /\ TLCSet(1,
  2))`, `tlcset-decided-first-disjunct`), answers, also beside an Assert of a failure
  (`tlcset-part-fails-before-print`). The engine's probe isn't made of a definition that reaches
  TLCGet, JavaTime, TLCExt's builtins but `Assert`, or IOUtils's and Json's (`UNPROBED_EFFECTS`),
  nor of one that reaches TLCSet where TLC may evaluate it later than the definition's own
  evaluation reaches it, or never (`reaches_deferred_tlc_set`: in a function constructor's body
  over a set TLC may build at once, a filter's predicate, a LAMBDA, a LET's definition or an
  argument of an operator the spec defines), where the engine may meet it in another order than
  TLC (`<<[i \in 1..2 |-> TLCSet(1, i)], PrintT(7)>>[2]` prints 7 as TLC starts, as the
  application keeps the constructor lazy, where the engine builds it), nor of one that names a
  definition the engine computes as it starts with effects, which TLC may compute after it and
  inside it; those decline as before. A probe the engine stops at a limit of its own on, before
  any effect, where TLC fails (`[a |-> 1] = <<1>>`, `(0..2147483647) = {}`, `[n \in Nat |-> n] =
  [n \in Nat |-> n]`, `Seq({1}) = {}` as the first conjunct before `PrintT(9) /\ TLCSet(1, 2)`),
  answers where the trace evaluator, computing the definition as TLC does as it starts, after the
  startup's definitions, fails on it with TLC's own error and without a print, a warning, a draw,
  a register's write, or a builtin whose effect the startup doesn't see
  (`Reporter::fails_register_probe`, `Rebuilder::confirm_failing_probe`): TLC swallows that
  failure, as it would one the engine found, and the definition is computed again at each use,
  where the engine leaves the same limit to the trace evaluator as before. Where the evaluator
  computes the part instead (`SUBSET (1..40) # {}`, `[n \in Nat |-> n][3] = 3`), goes past it to
  a print or TLCSet, or can't follow it, the probe declines as before. Still declined, where main
  matches: a TLCSet the engine doesn't place in TLC's order whose key is another expression of a
  bound name (`[i \in 0..2 |-> TLCSet(i + 1, i)]`) or that sets nothing as TLC starts
  (`PrintT({x \in [i \in 1..2 |-> TLCSet("s:a", i)] : TRUE})`), and one in a constructor over
  `Nat` the engine doesn't compile there (`([i \in Nat |-> TLCSet(1, i)] # 1) /\ PrintT(9)`). Declined where main matches by chance: a reader that
  prints of a definition TLC computes as it starts without reaching its TLCSet (`D ==
  (Len(<<1>>) = 1) \/ (PrintT("x") /\ TLCSet(1, 2))`, `Test == PrintT(<<D>>)`), which TLC
  computes and prints once as it starts and keeps, where main prints at each read (with `ASSUME
  Test` twice main prints `<<TRUE>>` twice, TLC once), and `D == TLCSet("exit", 2) \cup
  PrintT({1})`, whose print TLC shows once where main shows it at each read (`PrintT(<<D, D>>)`
  prints `{1}` twice on main, once on TLC). A shape whose draw TLC makes first,
  as `D == (1 = 1) /\ RandomElement(1..1000) = 1 /\ TLCSet(1, 2)` or, beside another draw, `D ==
  (RandomElement({1}) = 1) \/ (PrintT("x") /\ TLCSet(1, 2))`, still declines: main matches it only
  by chance, while nothing else draws, as it ignores TLC's startup draw, which moves TLC's generator
  even for a set of one element: with `Test == PrintT(RandomElement(1..1000)) = TRUE /\ D` TLC
  prints 919 and main 731. But a junction's
  operand whose only effects are draws written in it of RandomElement, also of `SUBSET S` for a
  set S of at most 12 elements (each subset in turn), or of Randomization's RandomSubset(k, S)
  for a natural k at most S's size (each subset of k elements in turn), which decides the
  junction for every element each draw may take, where nothing else in the spec draws, answers
  (`decides_for_every_draw`): `(RandomElement({1}) = 2) /\ TLCSet(1, 2)`, `(RandomElement({0, 2})
  = 1) /\ TLCSet(1, 2)`, `(<<RandomElement({0, 2})>> = <<1>>) /\ TLCSet(1, 2)`,
  `(RandomElement({1}) = 1) \/ TLCSet(1, 2)`, `(RandomElement(SUBSET {1, 2}) = {3}) /\ TLCSet(1,
  2)` and `(RandomSubset(1, {0, 2}) = {1}) /\ TLCSet(1, 2)`, in all five contexts. A RandomSubset
  of a count past the set's size, which TLC rejects, or of a power set of more than 12 elements,
  still declines. The front end's evaluator computes the operand once
  for each combination of elements (up to 4,096, so `(RandomElement(1..2000) = 2001) /\ TLCSet(1,
  2)` answers, and `1..5000` declines), comparing two tuples written out of integers,
  strings or booleans element by element (a tuple holding other elements declines: "a tuple's
  elements TLC may not compare"); TLC reaches no TLCSet, whatever it draws, and keeps the
  value, which the engine computes alike at each use, drawing there too, where no other draw shows
  the generator's state that leaves. Draws written in the junction's operands after the deciding
  one, which neither TLC nor the engine reaches, don't count as another draw:
  `(RandomElement({0, 2}) = 1) /\ TLCSet(1, RandomElement(1..5))` answers. One that may hold
  (`RandomElement({1, 2}) = 2`), draws past the deciding operand elsewhere (`... /\
  (RandomElement({0, 2}) = 1) /\ TLCSet(1, 2)` twice, or `TLCSet(RandomElement({1}), 2)`), draws a value the evaluator doesn't hold (`RandomElement({<<1>>}) =
  <<2>>`), sits under a LET (`LET r == RandomElement({1, 2}) IN (r = 3) /\ TLCSet(1, 2)`), behind
  an operator (`Op(s) == RandomElement(s)`) or after a print (`PrintT("x") /\ ...`), or beside
  another draw anywhere in the spec, still declines, as does `[k \in {1, 2} |-> k] = (<<1>> @@ <<RandomElement({0, 2})>>) => TLCSet(...)`,
  of functions the evaluator doesn't compute. Of these, main matches two only by chance, as the
  jar shows at other seeds (`-seed 1, 2, 3, 7, 99, 12345`, in the five contexts):
  `(RandomElement({1, 2}) = 2) /\ TLCSet(1, 2)` is wrong in main at seeds 1, 3 and 99, and
  `(<<RandomElement({0, 2})>> = <<0>>) /\ TLCSet(1, 2)` at 12345 (and as the next-state relation at
  every seed). The others main matches at every seed, so they are declines to win back, not by
  chance: the operand under a LET, behind an operator, after a print or holding tuples, the
  implication above, and `(RandomElement({1}) = 2) /\ TLCSet(1, 2)` beside `Z == RandomElement(1..10)`,
  whose value differs in the engine (which draws it before the operand's draw) but shows
  nowhere. Where such a definition is the first assumption itself, which nothing else names
  (no definition, no other assumption, no configuration entry), and it is the one register probe
  of a startup in which nothing else has an effect, no dependent, predicate or symmetry
  (`tla_ir::Startup::is_probe_assumed_once`), the engine's probe that completes without reaching
  a TLCSet, to a boolean, a number or a string, answers whatever it printed or drew: TLC made
  those prints and draws as it started and kept the value the assumption reads, and the engine,
  keeping nothing of the probe (it puts the generator back and drops its prints), computes it
  again at the assumption, from the same generator, with the same prints in the same place
  (`Test == ((RandomElement({0, 2}) = 1) /\ TLCSet(1, 2)) \/ PrintT(RandomElement(1..1000))`,
  `(RandomElement(SUBSET {1, 2}) = {3}) /\ TLCSet(1, 2)`, `(RandomSubset(1, {0, 2}) = {1}) /\
  TLCSet(1, 2)` and `PrintT("a") \/ TLCSet(1, 2)` as an assumption). One that reaches a TLCSet
  there, which TLC fails on after its effects and computes again at the assumption with them,
  one the first assumption doesn't read alone, once, by name (`ASSUME Test` twice, `F == Test /\
  TRUE` beside it, an earlier `ASSUME PrintT(...)`), or beside another startup effect (`E ==
  RandomElement(1..10)`), still declines. A probe may read a definition the engine computes as
  TLC starts with effects (`Startup::definitions`) where TLC computes that one before the probed
  definition: TLC keeps its value and the probed definition reads it, as the engine's probe and
  every later use do (`D == RandomElement({0, 2})` before `Test == (D = 1) /\ TLCSet(1, 2)`, in
  all five contexts, and `D == RandomElement({0, 2})` before `E == D + RandomElement({5})` and a
  probe of E). One TLC computes after the probed definition (of a module it processes later),
  which TLC computes inside it with its effects first, still declines, as does one whose
  computation failed, which the engine computes again inside the probe with its effects. Still declined where main matches (see "Declines to win back
  where main matches"): `(PrintT("a") /\ RandomElement({0, 2}) = 1) /\ TLCSet(1, 2)` in the init,
  invariant and property contexts, and, as assumptions, two register probes (`D ==
  (RandomElement({0, 2}) = 1) /\ TLCSet(1, 2)` with `Test == PrintT(<<D,
  RandomElement(1..1000)>>)` or `Test == D \/ PrintT(<<D, D>>)`), a probe that prints a draw
  beside a startup definition that draws (`D == RandomElement({0, 2})` with `Test == ((D = 1) /\
  TLCSet(1, 2)) \/ PrintT(<<D, RandomElement(1..1000)>>)`), and a print or a draw the engine
  doesn't compile in a probe (`(RandomElement({x \in 1..3 : PrintT(x)}) = 5) /\ TLCSet(1, 2)`,
  the `@@` implication above), and a probe the first assumption reads under an operator, at one and
  four workers (`A == (RandomElement({0, 2}) = 1) /\ TLCSet(1, 2)`, `(RandomElement({0, 2}) \in
  {0, 2}) \/ TLCSet(1, 2)`, `(RandomElement({1}) = 1) \/ TLCSet(1, 2)`, `(RandomSubset(1, {1,
  2}) = {}) /\ TLCSet(1, 2)` with `Test == PrintT(A)`, or `(RandomElement({0, 1}) = 5) /\
  TLCSet(1, 2)` beside `B == RandomElement(1..3)` with `Test == PrintT(A) /\ PrintT(B)`), where
  `is_probe_assumed_once` holds only for the assumption that is the probe's name.
  One
  that reaches AssertError and an effect ("...with AssertError and effects"),
  as `D == PrintT(1) /\ AssertError("x", 1)`, but `PrintT(AssertError(s, e))` of a string written
  out, which never fails, or a conjunction of such prints and of `AssertError(s, e)` compared with
  TRUE or FALSE, which never fails either (`AssertError("", 1) = FALSE /\ PrintT(AssertError("", 1
  \div 0))`, which main matched), that only the first assumption reads, as the assumption itself,
  where no other constant definition TLC computes as it starts has an effect
  (`is_assumed_print_once`). A comparison with another value (`AssertError("", 1) = 1`), a
  disjunction, and a definition read twice (`ASSUME Test` twice, where TLC prints once) decline.
  A TLCSet whose key has no effect and fails as TLC builds it, before the value it evaluates
  next, fails before any effect too, where the front end's evaluator finds the key fails
  (`is_key_failing_as_built`): `TLCSet(1 \div 0, PrintT(1))`, `TLCSet(<<1 \div 0>>, PrintT(1))`
  or `{1 \div 0}` (a tuple or a set enumeration fails at its first element that fails), also
  through a definition named without arguments or as the first operand of a junction
  (`tlcset-key-fails-as-built`); and one whose key has no effect and whose value fails first,
  as `TLCSet(Nat, TLCSet(1, 2))`, whose inner TLCSet throws as TLC starts before the outer one
  sets anything (`tlcset-value-fails-first`). A key whose failure the evaluator can't compute, as
  `<<1, 2>>[3]` or `[i \in {1} |-> 1 \div 0]`, still declines (see "Declines to win back where
  main matches"). A key built
  without effect that is neither an integer nor a string (a set, a function, a record, a tuple,
  a model value, `Nat`, `Int`, `STRING`, `BOOLEAN`, `SUBSET`, `UNION`, `\cup`, `\cap`, `\` or
  `Seq` of such), as `TLCSet(Nat, 1)`, fails first too, whether TLC rejects it or fails building
  it (`tlcset-key-*` fixtures). A definition whose only TLCSet is of "exit" or "pause" and a
  literal other than TRUE beside a print still declines (see "Declines to win back where main
  matches"). Since
  `processConstantDefns` computes every such definition, read or not, an unread `D ==
  TLCSet("-Dbar", 7)` sets the system property bar as TLC starts, which `TLCGet("-Dbar")` then
  reads as `"7"` (the last such definition in TLC's order wins, and a failure after the set,
  which TLC swallows, keeps it), where the engine computes no unread definition. The front end
  declines a definition TLC computes as it starts, but where it fails first, that reaches
  TLCSet of a "-D" key a TLCGet the model reads names, or of a key it computes ("a constant
  definition TLC computes as it starts that sets a system property TLCGet reads"), but past a
  definition that sets nothing (`sets_nothing_at_startup`), as `D == (1 \div 0 = 1) /\
  TLCSet("-Dbar", 7)` or `D == TLCSet(1, 2) /\ TLCSet("-Dbar", 7)`, which TLC never reaches, and
  a root definition without other effects that the constant evaluator, computing TLCSet as
  TLC does as it starts and leaving a system property's uncomputed, computes to a value or a
  failure: it never reached the set, as `S(k) == (k \div 1 = 1) /\ TLCSet("-Dbar", k)` with `D
  == S(4)`, or `D == LET a == 1 \div 0 IN a = 1 /\ TLCSet("-Dbar", 7)` (`system-property-false-
  guard`). With the guard holding (`k \div 1 = 4`) it declines, where main prints `"-Dbar"` and
  TLC 4. An
  AssertError whose message is a string written out
  and whose expression, written where no name is bound around it, reads no state or register and
  has no effect, the trace evaluator computes once as the search starts
  (`Reporter::check_constant`), which declines where it fails or prints; one whose message isn't a
  string written out fails as TLC's `Assert.check` does, which the trace evaluator words. Such an
  expression may read TLCGet of a register written out as a number where the spec sets no
  register (no TLCSet, TLCGetAndSet, _Track or Java class of the user's): every thread of TLC
  finds it unset and fails alike, as `TLCGetSet.TLCGetEval`'s Java method. An assumption's
  TLCGetAndSet of a key TLCSet rejects, as `TLCGetAndSet("foo", +, 1, 0)`, fails as TLCSet does
  once Op is computed, which an assumption reports without the call stack that would hold
  TLCExt's frames; elsewhere it still declines.
- a constant definition TLC computes as it starts whose TLCSet is only in a branch TLC doesn't
  take, of a condition the front end's evaluator computes (`IF FALSE THEN TLCSet(1, 2) ELSE e`,
  `FALSE /\ TLCSet(1, 2)`, `\A i \in {} : TLCSet(1, 2)`), or which names such a definition, and
  that reaches an effect in a branch TLC takes (a print, a draw at random, TLCExt's registers;
  not the clock alone, which nothing shows). TLC tells the level by where TLCSet is written, so
  `processConstantDefns` computes such a definition once as it starts, read or not, with its
  effects, and keeps its value (computing it again at each use where it fails). The front end
  counts TLCSet state-level wherever it is written, so the engine computes it only where the
  model reads it: with `D0 == IF FALSE THEN TLCSet(1, 2) ELSE TRUE`, an unread `D2 == D0 /\
  PrintT(3)` printed nothing where TLC prints `3`, `Test == D1 /\ D1` over `D1 == D0 /\
  PrintT(3)` printed `3` twice where TLC prints it once, and `D1 == D0 + PrintT(1)` over `D0 ==
  IF FALSE THEN TLCSet(1, 2) ELSE 0` printed `1` once where TLC prints it four times; main
  printed the same. The front end declines such a definition ("a constant definition TLC
  computes as it starts with effects and TLCSet only in a branch it doesn't take"). Main matched
  where the model reads the definition once and nothing prints between TLC's start and that
  read, by chance: `Test == D1` over `D1 == D0 /\ PrintT(3)` prints `3` once both ways, but
  `Test == PrintT(4) /\ D1` prints `3` then `4` in TLC (both definitions computed as it starts,
  in order) and `4` then `3` in main, and `Test == D1 /\ D1` prints `3` twice in main, once in
  TLC; a draw such a definition makes moves TLC's generator before the constant definitions
  after it draw, so with `D1 == D0 /\ RandomElement(1..1000) > 0` and `E ==
  RandomElement(1..1000)`, `Test == D1 /\ PrintT(E)` printed another number than TLC's in main
  (probed against the jar in all five contexts, 2026-11-19). A print only in the branch TLC
  doesn't take, as `IF FALSE THEN TLCSet(1, 2) /\ PrintT(1) ELSE TRUE`, still answers. Where
  the first assumption is the definition's name alone, which nothing else names, followed
  through definitions whose body only names another one named nowhere else (`Test == D`), and no
  other definition TLC computes as it starts has an effect, a register's write among them, and
  none reaches TLCGet, the clock or another builtin the startup doesn't count (`get_assumed_once`),
  the definition answers: TLC computes it once as it starts, and the engine once, at the
  assumption, with nothing between: `D == [y \in 1..0 |-> TLCSet(1, y)]` (or `{y \in {} :
  TLCSet(1, y)}`, `{TLCSet(1, y) : y \in {}}`, `\A y \in {} : TLCSet(1, y)`) with `Test ==
  PrintT(D)`, and `D == PrintT(1) /\ [y \in {} |-> TLCSet(1, y)] = <<>>` with `Test == D`, as an
  assumption. In the other contexts, and where the definition is read twice (`Test == D /\ D`)
  or beside another print, it still declines; main matches some of those in the other contexts
  (`IF FALSE THEN TLCSet(1, 2) ELSE PrintT(3)` read by the initial predicate), declines to win back.
- a predicate the configuration names (an invariant, a property, a constraint, an action
  constraint, a POSTCONDITION, INIT or NEXT) that reaches TLCSet, taken branch or not, and no
  variable or TLCGet. TLC counts it constant-level and computes it as it starts: an invariant
  that is TRUE is the warning 2149 and is never checked, and any other value is
  TLC_CONFIG_ID_HAS_VALUE (2230, `The invariant of Inv is equal to FALSE`); a POSTCONDITION TLC
  rejects with a RuntimeException. The front end counts TLCSet state-level and checks the
  predicate in each state, so main and the base printed no warning for `Inv == \A i \in {} :
  TLCSet("pause", TRUE)` and reported `Inv == FALSE /\ TLCSet(1, 2)` as violated by the initial
  state. The front end declines such a predicate ("a predicate the configuration names that TLC
  computes as it starts, constant but for TLCSet") but where TLCSet fails first
  (`fails_first_at_startup`), where the constant evaluator, computing TLCSet as TLC does before it
  has a checker (a number fails, "exit", "pause" and a named register give TRUE, any other key
  fails), finds the predicate failing, and where a constraint or an action constraint it computes
  is TRUE, which TLC drops and the search finds holding everywhere. Where the evaluator can't
  compute the rest, as `Inv == TLCSet("pause", FALSE) /\ 3`, it declines, though main matches
  there because TLC fails on `3` as it starts and checks the invariant in each state; main is
  wrong on the neighbour `TLCSet("pause", FALSE) /\ TRUE`, which TLC warns of.
- a print (Print, PrintT, AssertEq's) or a ToString of a value that holds the install of
  TLCGet("config"), in a model that may read it ("printing TLC's install, where its jar is").
  TLC writes the path of its jar there (`TLCGlobals.Version.installLocation`), which a native
  checker has none of and writes "unknown". The suite's transcript normalizes the field only
  inside a message's body, where an Assert or a failure prints the record, so
  `PrintT(TLCGet("config"))` printed "unknown" where TLC prints its jar's path. A value built from
  the install's text otherwise, as `Len(TLCGet("config").install)`, still answers.
- a comparison the store makes of a typed model value with another value now stops the search
  as a failure TLC reports ("typed model value"), which the trace evaluator words or declines
  where it finds none ("it didn't fail"); an assumption that meets it stays the caller's, as
  TLC compares `Nat = m` for a typed `m` without failing (`UserValue.equals`). The trace
  evaluator follows such a failure, and one of differently typed model values, into the sets TLC
  compares by their parts (`SubsetValue.equals`, `SetOfFcnsValue.equals`, `SetOfRcdsValue.equals`,
  `SetOfTuplesValue.equals`), into the `normalize` or `elements` of a set enumeration TLC holds
  unnormalized wherever an equality, an enumeration or `SubsetValue.member` reaches it, and into
  the `cup` of such a set, which is `Reducible` too; and `UNION` of a set enumeration of set
  enumerations, normalized or not, combines them with `equals` as `UnionValue.union` does. Each
  adds the frame of that set to TLC's fingerprint stack, which main left out in Next (`{T} \X {1}
  = {1} \X {1}`, `[{1} -> {T, 1}] = {}`, `{T, 1} \in SUBSET {1}`, `UNION {{T}, {1}} = {1}`).
- a function TLC holds as a `FcnLambdaValue` (OPCODE_rfs always, OPCODE_fc under
  `EvalControl.KeepLazy` or over a domain that isn't `Reducible`) whose body prints, reads or sets
  a register or draws at random as the trace evaluator builds it, unless an operation that forces
  it follows ("effects in the body of a function TLC keeps lazy (FcnLambdaValue)"); and a LET's
  function the evaluator builds or applies again where TLC's LazyValue keeps it, whose body or
  domain has such an effect ("a function a LET defines, used again, whose body has effects TLC has
  once"). TLC evaluates a lazy function's body only as it uses the value, `apply` and `select` at
  one key each time, `toFcnRcd` (from `compareTo`, `equals`, `fingerPrint` and `toString`) once
  for the object, cached in `fcnRcd`, and `getDomain` and `deepNormalize` not at all; `Print` and
  `PrintT` print a copy (`deepCopy`), which builds it again and leaves the object unforced, and
  `takeExcept` makes a copy too. The evaluator builds the function where it evaluates it, so the
  body's effects come there. It keeps them (`construct_function`, `force_lazy_prints`) only where
  the operation the function is an argument of forces it with nothing between them having effects:
  `@@` (`CombineFcn` forces both arguments, after `OpValue.eval` evaluated both), `=` and `#` (the
  first argument, and the second where the first is a function, tuple, record, integer, string or
  boolean, which converts or prints it), `\in` and `\notin` of a set of functions, `Seq(S)`, a
  written set enumeration of such values, a filter of one or a union of two (`SetOfFcnsValue`,
  `Sequences.member`, `ValueVec.search`), `ToString` and the prints of the functions it holds once
  each, in the order the evaluator built them where there are several and nothing sorts them on
  the way. A lazy body that built lazy functions of its own and printed only through them hands
  them on. An application takes the lazy function built for it whose body printed at the argument
  only, nothing having effects in between (`FcnLambdaValue.apply` evaluates that body after the
  argument). A LET's function, which TLC holds once, the evaluator builds again at each use (as TLC
  builds a copy, or applies the unforced function) only while no use forced it and the prints
  named it directly; two of its uses an operation forces at once decline. Anything else, an
  application, select or EXCEPT while one waits, a LET definition or an argument read again from
  where the evaluator keeps its value (one it doesn't keep, as `Tool` expands a LazyValue directly
  where the next state is null, both build again; but see below for one whose value is a function
  constructor), a failure before the force, and an ALIAS that
  prints and holds a function of unknown key order ("an ALIAS that prints and holds a function of
  unknown key order", `CombineFcn`'s unnormalized result, which main printed sorted too),
  declines. So `[s \in SUBSET {1} |-> Print(<<"L", s>>, 0)] @@ Print("X", <<>>)`, where TLC
  prints `"X" <<>>` before the lines of the body, declines, as `L @@ (R @@ <<>>)`, a right operand
  that fails, and a right constructor whose domain prints do (main declines them too), while
  `PrintT(L)`, `<<L>>`, `L = <<>>`, `<<>> = L`, `1 = L`, `L \in {<<>>}`, `F @@ <<>>` of a
  recursive `F`, `LET C[s \in SUBSET {1}] == ... IN PrintT(C) /\ PrintT(C)`, `\E y \in {L} :
  PrintT(y)` and `[i \in SUBSET {1} |-> IF i = {} THEN Print(i, 1) ELSE 1][{}]` answer as TLC.
  Fuzzing 737 specs against the jar and main at -workers 1 and 4, 1,474 runs (the 352
  specs of the review and 385 more of these shapes, their neighbours and the copies, forces,
  applications and shares between them), answers none wrong but `[t \in SUBSET {2} |-> 1] @@ [s
  \in SUBSET {1} |-> 0]` in an ALIAS, which prints no lazy body and which main prints wrong too.
  A LET definition or an argument whose value is one function constructor TLC keeps lazy, whose
  body printed, TLC holds as one FcnLambdaValue in its LazyValue, and a print forces a copy of it
  (`deepCopy`), which leaves it unforced: TLC builds it again at each use a print forces, as the
  evaluator does where it builds the thunk's value again (`Frame::is_thunk_unforced`), where the
  build has no effect but the body's and the print reaches the function by the thunk's name, or a
  tuple or record of such names, or an IF or a CASE whose arms are (`PrintT(IF TRUE THEN C ELSE
  C)`). A thunk that names another (`LET E == C`, a chain `F == E`, or an operator's parameter
  bound to `C`) holds TLC's same FcnLambdaValue, its LazyValue reading the one the other holds: the
  evaluator keeps the build as the innermost thunk's, so a force through any of the names marks it
  forced, and a later use of any of them builds it again through the inner one or declines with
  it. A use that forces TLC's function in place (an equality, `@@`, ToString, or a print of a set
  holding it, `PrintT({E})`) forces the one build the evaluator holds of it, once, and the
  thunk's later uses, under any of its names, decline. So
  `PrintT(C) /\ PrintT(C)`, `<<C, C>>`, `[a |-> C, b |-> C]`, `Op(L)` with `Op(c) == PrintT(c)
  /\ PrintT(c)`, `PrintT(C) /\ C = <<>>` and `PrintT(C) /\ PrintT(C @@ <<>>)` answer, in an
  assumption and elsewhere, where `main` matched them too. A LET's function applied before its
  use as a value TLC keeps unforced (`FcnLambdaValue.apply` evaluates the body at the key only),
  with the domain it evaluated there: the use builds it as the evaluator does where the domain has
  no effect, so `LET C[s \in SUBSET {1}] == Print(<<"L", s>>, 0) IN C[{}] = 0 /\ PrintT(C)`
  answers; one over a domain TLC reduces (`C[s \in {1, 2}]`, `C[s \in 1..2]`), which the
  evaluator builds otherwise, or whose domain prints, still declines ("a function a LET defines,
  which TLC kept lazy where it first applied it"). Still declined where `main` matches:
  `\E y \in {C} : PrintT(y)` before `PrintT(C)` and `PrintT(CHOOSE f \in {C} : TRUE)` (a set the
  evaluator takes for one that may force it), an IF one of whose arms isn't such a name
  (`PrintT(IF FALSE THEN {C} ELSE C)`, `IF TRUE THEN C ELSE 1 \div 0`), `PrintT([x \in {1} |-> C])`
  before `PrintT(C)` (a lazy function in the body of another), `PrintT(g) /\ g[{}] = 1` ("a function TLC keeps lazy in an argument, used but
  applied", the function the application holds in place, which the evaluator doesn't follow),
  `nested @@ <<>>` (lazy functions in the body of one `@@` forces) and `<<L>> = <<<<>>>>` (a force
  inside the comparison). `<<R, RandomElement({1, 2})>>` declines too: `main` makes TLC's three
  draws in another order, which shows only at a seed whose draws differ; at the suite's seed all
  three give 2, so `main` matches that one (`ASSUME PrintT(<<[s \in SUBSET {1} |->
  RandomElement({1, 2})], RandomElement({1, 2})>>)`) by chance.

#### Functions TLC keeps lazy, built or applied

TLC keeps a function constructor as a `FcnLambdaValue` where its domain isn't Reducible or the
control is KeepLazy, and fails on it only where it builds it (`toFcnRcd`), applies it (`apply`)
or selects a key of it (`select`, for EXCEPT). The trace evaluator follows these:

- An EXCEPT of one, outside an assumption, whose `select` fails inside a value's own method with
  a source declines: a comparison with an EXCEPT key that is a tuple, a record, a function or a
  set (`LET f == [x \in Nat \cup {<<1>>} |-> x] IN PrintT([f EXCEPT ![<<1>>] = 5][1])`, keys
  `[a |-> 1]`, `![1, 2]`), "a failing comparison of a lazy function's EXCEPT key that has a
  source"; a failing test of a domain TLC built from an expression (`[x \in {1, 2} |-> x]`, `Nat
  \cup STRING`) at the key, "a failing test of a lazy function's domain TLC built from an
  expression", as `apply` declines it; and a failing test of a domain the evaluator built at a
  key that has a source (`S == {1, 2}` with `![{1}]`), "a failing test of a lazy function's
  domain at a key that has a source". TLC reports these as a value it can't fingerprint, whose
  stack ends at the value's source (`FingerprintException.getNewHead`), where the binary printed
  the nested expressions without it (main declined these, or printed the same wrong output for
  the `Nat \cup STRING` domain).

- Building one over a domain it can't enumerate fails as `toFcnRcd` does: `FcnParams.size` asks
  each domain's `size` (`Attempted to compute the number of elements in the integer 0.`, a
  filter's or a union's enumeration failure, ...), then `FcnParams.elements` rejects a value
  that isn't `Enumerable` (`The domains of formal parameters must be enumerable.`, or `...of
  the parameters...` for several). `toTuple` fails on a domain whose `toSetEnum` fails or is
  null. An overflow of the product of the sizes, a build that goes on to the body, and a domain
  that enumerates empty decline ("built a function over an infinite set").
- Building one over Nat, Int, Real or STRING outside an assumption fails in `UserValue.size`,
  which throws the failure on as a FingerprintException where a node gave that set a source.
  TLC shares each of these as one object, so the source is the last one a node gave it, as
  `{} \cup Nat` gives Nat the union's. Where a node of the replay gave one of them a source,
  that failure declines ("a function TLC builds over a domain it shares, which a node gave a
  source"), as in `[x \in {} \cup Nat |-> x] = [x \in {1} |-> x]` or a membership of it in
  `[Nat -> Nat]`. A Java method that words the failure as its own, as Bags' `IsABag`, and an
  assumption, which TLC evaluates without a call stack, still answer.
- Building one over a domain that fails to count in a method of its own, as `Nat \X Nat`,
  `{1} \X Nat` or `SUBSET Nat`, throws the failure on as a FingerprintException with the source
  of the node that built that domain (`[<<a, b>> \in Nat \X Nat |-> 1] = <<>>` heads the stack
  with `Nat \X Nat`), which the replay doesn't place for a function it holds lazy. Where the first
  domain `FcnParams.size` fails on has a source, the failure declines ("a function TLC keeps lazy
  over a domain with a source that fails to count"); main declined these. One that fails on a
  domain with no source, as `[x \in {}, y \in Nat |-> 1] = <<>>`, answers.
- `r.f` of a constructor over an `IntervalValue` fails as the `FcnRcdValue` it builds does
  (`Attempted to apply function with integer domain to the non-integer argument "f"`).
- Applying, or the first EXCEPT of, a constructor written in place that TLC keeps lazy over an
  interval or a lazy set asks the set's `member` for the argument first, which fails as that
  method does (`Attempted to check if the value: ... is in the integer interval 1..2`,
  `Attempted to check if the non-enumerable value ... is element of ...`). Outside an assumption
  TLC heads that failure with the set's source, which the replay doesn't place ("the membership
  in the domain of a function TLC keeps lazy"); a membership with effects, such as a filter's
  predicate that prints, declines ("the membership in the domain of a function TLC keeps lazy,
  with effects").
- A constructor of one name over a lazy set that isn't Reducible, whose body fails at a key
  with TLC's own failure and no effect before it, is held unbuilt, as TLC holds it, without a
  call stack: printing it prints `[x \in S |-> <expression ...>]` (`toString` swallows the
  build's failure), applying it evaluates the body at the argument alone, and building it
  declines where the build would reach the body.
- A constructor TLC keeps lazy where it is applied (KeepLazy) over a set enumeration, such as
  `UNION {{1}, {2}}`, which `UnionValue.union` combines into one: outside an assumption, a test of
  the argument in that domain that fails is `SetEnumValue.member`'s FingerprintException, headed
  with the set's source, which the replay doesn't place ("a failing test of a lazy function's
  domain TLC built from an expression"). An interval, which `..`'s Java method builds without a
  source, reports the test's own failure.
- A LET definition (or an argument) whose constructor an application kept lazy holds that
  FcnLambdaValue in its `LazyValue` cache (`EvalControl.semanticallyEquivalent` ignores
  KeepLazy), so a later use reads it unbuilt: `DOMAIN` reads its domain, printing it swallows the
  build's failure, while equality builds it and fails. The evaluator builds it again at such a
  use; where that build fails, it declines ("a function TLC keeps lazy, applied, then used where
  its build fails").

- Applying an EXCEPT, written in place, of such a constructor over an interval at an integer
  outside it fails as `FcnLambdaValue.apply` does, printing the function it builds (`In
  applying the function <<7, 2>>, the first argument is: 2147483647 which is not in its
  domain.`).
- `Permutations` of a function, which has no `toSetEnum`, prints it in TLC's
  `TLC_MODULE_APPLYING_TO_WRONG_VALUE` message, a lazy one as its `toString` builds it or not.
  One holding a set enumeration TLC can't normalize fails printing it, at a comparison the
  evaluator doesn't place, which declines ("Permutations of a function holding a set TLC can't
  print"); an earlier build printed `<<{1, "a"}>>` there.

- A test of a lazy function's domain that fails reports the domain's own failure where no
  value has a source: as TLC starts and in an assumption, which TLC evaluates without
  `CallStackTool`. Elsewhere a domain built from an expression still declines ("a failing test
  of a lazy function's domain TLC built from an expression").

`IntervalValue.cap` and `diff` walk the whole interval, testing each integer's membership in the
other operand. Of an interval too long for the evaluator to walk, against an interval or a set
enumeration of integers alone, whose tests compare integers and can't fail, the evaluator keeps
what the walk keeps without walking it, as `(3 .. 2147483647) \cap (0 .. 1)`, failing past
`TLCGlobals.setBound` as `ValueVec` does. Against any other set the walk still declines ("an
interval too large to build").

A comparison (`<`, `>`, `<=`, `>=`) that fails printing its operand fails in the Java method of
the module TLC loaded, Integers' over Naturals'. The front end now marks `<`, `>` and `<=` as
Naturals' methods where Integers doesn't replace them, as it marks `+`. Before, a spec whose
only arithmetic was `<` named no module, and the evaluator printed the operand's
`TLC_MODULE_ARGUMENT_ERROR_AN` text, as `Test == (1) < ({1, "a"})` with `ASSUME Test` (the earlier
build printed the same wrong text; TLC fails in `Integers.LT`, comparing "a" with 1). Where neither
module can be named it declines ("a comparison's failing print, of Naturals or Integers").

#### A constant definition the engine fails on that TLC computes as it starts

TLC computes each constant definition as it starts (`processConstantDefns`) and keeps the value,
which every use reads. The engine evaluates one without effects where it is used, and some it
can't compute where TLC can: `1 \in UNION {{"a"}, 1..2}` asks the interval first, which answers,
where the engine compares the elements of the union and fails; `DOMAIN [x \in Nat, y \in {1} |->
x] = Nat \X {1}` compares two lazy sets the engine would enumerate. In an assumption the trace
evaluator already computed these, but as the initial predicate, the next-state relation, an
invariant or a property the search stopped and the replay found no failure ("evaluating the
failure again: it didn't fail"). Now, where the engine fails on a boolean constant definition TLC
computes as it starts (`NORMALIZED`, not one the configuration substitutes), which names nothing
with an effect, no TLCGet or other builtin whose value depends on when TLC evaluates it, no
ENABLED and no state, the trace evaluator computes it as TLC does there (`Settings::adopter`,
`compute_constant_definition`): where it computes a boolean without a print, a warning, a draw
or a register write, every use reads that value, once per run, and the warnings the engine
printed before it failed are dropped; anything else keeps the engine's failure and its replay
(the trace evaluator's reasons there: `a constant definition with effects or warnings`, `a
constant definition that isn't a boolean` and `a definition the IR doesn't have`; and `a constant
definition TLC computed at startup with effects, walked` where the replay, computing such a
definition again, would write a register or draw).
The search no longer splits such a definition into its conjuncts where an invariant or a
property names it, so each use reads the kept value. The initial predicate and the next-state
relation test such a definition as a guard where they reach it, rather than walk its body: TLC's
`getInitStates` and `getNextStates` look the name up and find the value, so `(M /\ x' = 1 - x)
\/ (1 = "a" /\ x' = x)` generates the first disjunct's successor before it fails on the second
(before, the engine failed on M there and counted no successor, a wrong output main printed too).
A CASE whose every arm is a boolean is now one, as an IF is, so a CASE definition is read the same
way. One TLC fails on as it starts it leaves as the definition, whose body those walk; the trace
evaluator's walk now walks it too (`is_kept_at_startup`), where it tested it as a guard: `M == 1
= 1 /\ 1 = "a"`, conjoined first in the next-state relation, places the failure inside the frame
of `1 = 1`, as TLC does (a wrong output the base printed where main matched; `constant-*-next*`
startup_checks fixtures). A warning-only constant definition the
engine failed on before any warning at startup, other than at a limit of its own, is now
confirmed by the trace evaluator too (`unwarned_startup`): TLC may compute it and warn, as
`"a" \in UNION {1..2, {"a"}} /\ [<<1>> EXCEPT ![2] = 3] = <<1>>`, whose 2144 warning the startup
lost under `ASSUME` (a wrong output main declined); where the evaluator's startup warns or
prints on it, the model now declines ("a warning-only startup definition the search failed on
before a warning, that warns or prints here"); where it fails in a way it can't word, the
engine's answer stands, as before (`constant-*` startup_checks fixtures, recorded from the
jar).

#### Call stacks through an INSTANCE with substitutions

TLC's copy of a definition an INSTANCE with substitutions makes has a `SubstInNode` for its body
(`Generator.java`), which `CallStackTool` pushes as a frame at the INSTANCE; it reads a
declaration's substitute where the copy names the declaration, in that name's frame and then the
substitute's. The front end puts the substitutes in, so the IR holds no frame of the
`SubstInNode`; a substitute other than a name or a literal it puts in through a copy of its own
at each place the module names the declaration, which the IR writes as a `Reference` to the
substitute placed at that name (written once, as a root), and the trace evaluator evaluates such a
reference in a frame of its own before the substitute's. Where an enclosing INSTANCE's
substitution rewrites such a copy (an INSTANCE of a module that has one itself), the copy no
longer stands for the substitute as written, which the reference would read unsubstituted (with
`x <- y + 0` inside and `y <- z * 1` around it, `y` read as a variable of the outer module of
that name, a wrong output an earlier build printed): the front end lowers it as itself, without
the reference. A failure
whose frozen call stack has a frame that names such a copy (`Definition::SUBSTITUTED`), or a node
only the copies reach, declines, "a call stack within a definition an INSTANCE with
substitutions copies" (`Evaluator::check_substituted_frames`, which marks `CallStack::is_substituted`
apart from the other reasons), unless the stack can be printed with the `SubstInNode`'s frame put
in after each frame where the module's own expression names a copy (`substitution_frames`): a
copy that names another, as a definition of the instancee names one of its own, reaches TLC's
instancee's definition, which has no such frame. A frame in a substitute prints where the frame
before it is the reference at the declaration's name (`N == INSTANCE Inner WITH c <- 1 \div 0`
with the substitute used in `Init` or an invariant, or `v <- x + 1` primed in `Next`, which won
`checker/init/instance_substituted_expression` and `checker/prime/..._primed`; probes of 64
shapes, in each context and at 1 and 4 workers, match the jar or decline, where main was wrong
on 42). It still declines a frame in a substitute the evaluator reaches otherwise (as UNCHANGED
does), a copy of a copy
(an INSTANCE with substitutions of a module that has one itself, `Definition::NESTED_SUBSTITUTION`,
whose inner `SubstInNode` the IR doesn't keep), a copy's node no frame names, as where TLC
evaluates the `SubstInNode` itself (3 runs of the suite of `instance_substituted_expression`
and its neighbours), a first frame that names a copy, which may be the action `getActions` takes
the `SubstInNode` for, a selection through the INSTANCE whose frames reach the copy's own nodes
(the IR's LET without a range for it), and a copy given as an operator's argument. A LET
INSTANCE without substitutions puts no frame on the stack: its names forward to the instancee's
definitions with no range of their own, where one with substitutions forwards at the INSTANCE,
the frame of its `SubstInNode`. The arguments a LET INSTANCE's names forward, the instance's
parameters a copy passes on, and the application of an operator substituted for a declaration
with parameters are written nowhere, so evaluating a lazy argument or a substitute puts no frame
at the INSTANCE; a substitute is applied where the declaration is named, the frame TLC prints
before the substitute's own. A LET INSTANCE with substitutions of a module whose own INSTANCE
substitutes something (`LET L == INSTANCE Nest WITH d <- TRUE IN L!P(1)`, `Nest` having
`I == INSTANCE Inner WITH c <- d`) makes copies of copies, whose inner `SubstInNode` TLC prints
at `Nest`'s INSTANCE: a call stack with a frame that names such a copy declines as above. A node the copies share with the module's own definitions, which the IR writes
once, is reached within a frame that names a copy wherever a copy reaches it, so it alone doesn't
decline, unless some copy is given as an operator's argument, which is entered where the parameter
is applied. A named INSTANCE with substitutions gives every definition a copy with a
`SubstInNode`, even one a module without parameters made (`generateInstance`); the front end kept
that copy as the definition itself, so the module's own name for it, which TLC reaches without the
frame, counted as a copy: it keeps the copy apart now. The corpus's `etcd-raft/tla/MCetcdraft.cfg`
(etcdraft's own action reaching BagsExt's `FoldBag`, with `etcd == INSTANCE etcdraft`) answers
again; `B!Get`, `B!Fold(...)`, `Fold(B!Get, ...)` and a step of the copy still decline where TLC
prints the INSTANCE's frame (probed three-way against the jar and main, 2026-11-18). A failure TLC prints without the stack of the evaluation still answers: an
assumption, and an invariant or an action property of a successor (`doNextEvalFailed`), whose only
frames are those of TLC's replay of the expansion, where `replay_failed` declines such a stack. To win them back: keep the INSTANCE's
range for each copy and each substitute's declaration reference in the IR, and push both frames
where TLC does.

#### Call stacks of a selection

SANY makes a selection of a subexpression one node at the selector (`Generator.selectorToNode`):
a `$Nop` application of the part selected, or, where the selection gives an operator or a label
arguments (`V(1)!L`, `V(1)!1`), a LAMBDA's application, which `CallStackTool` pushes once. The
front end writes the latter as `LET $subexpression(p) == part IN $subexpression(1)`, and the part
under the LETs it is in (`V(p) == LET a == 1 IN L :: ...`); those LETs now have no range, so they
push no frame, where the frame of the selection was printed twice, and the label's frame after it
was dropped (main, with a frame less, printed the selection twice too). A selection through a copy
an INSTANCE with substitutions makes (`I!V(1)!L`, `I!X!L`, `J!V(1)!L` through an unnamed
`INSTANCE`) passes through the copy's `SubstInNode`, whose frame at the INSTANCE TLC prints right
after the selection's: the front end puts a `$Nop` at the INSTANCE around the part selected
(`Lowering::get_selection_substitution`), so the frame prints. A selection through a copy of a
copy, and one whose failure is in a substitute, print wrong; see "Known wrong outputs".

#### A constraint that fails on a successor

`Worker.addElement` evaluates the state constraints of every successor, seen or not, before the
invariants, and reports one that fails to evaluate as it does an action constraint: the trace to
the successor, then the error (`ErrorSite::Constraint`, `Site::Constraint`). As for an action
constraint, one the configuration binds to a constant or substitution declines, "a failing
constraint the configuration binds", and so do a failure with an ALIAS, and with an action
property, which the trace's replay doesn't check.

With several workers, TLC's other workers take each new successor a worker enqueues, and race it
to the stop: where a successor's constraint or action property fails after the worker enqueued
another state, or while another worker still expands one, the trace and the counts vary from run
to run of the Jar (`Next == x' = x + 1 \/ x' = x + 10` with `Con == x < 10 \/ x = 10 \/ 1 \div 0
= 1`). Under `-workers N` they answer only as the search expands its one initial state before it
finds a new successor where every state before it was the one new successor of the state
before (`StopCounts::is_lone_expansion`): the one initial state, or the end of a chain from it,
where each worker that enqueued a state had no other step to take, so no other has a state to
expand or a step to count (`Next == x < 6 /\ x' = x + 1` with the failure at `x' = 2` or 4: the
Jar prints the same in four runs of four, as one worker does). Elsewhere they decline "a
constraint, an action constraint or an action property that fails with several workers". An action constraint
has the same race: in `tests/action-constraint-failures` at `-workers 4`, the 23 specs whose
constraint fails past the first expansion print other traces and counts in the Jar than one
worker's (failDom_plain: 11 states generated, 7 distinct and depth 5, against one worker's 6, 4 and
3; most vary from run to run), where main declined failDom* and printed one worker's output for
the others; they now decline, and the 35 that fail on the first expansion still match. An
invariant and the next-state relation that fail past the first expansion have the race too, a
known wrong output from before, as main prints it: with `-workers 2`, `Next == B \/ \E i \in {1}:
A(i)` where B's successor is enqueued before A leaves `y` undefined, TLC reports 5 states
generated and none left on the queue, the binary 3 and 1. So does a plain invariant violation, and
a next-state relation that fails on a later state, under `-workers 4`: `Init == x = {}`,
`Next == x' \in SUBSET (x \cup {Cardinality(x)})`, `Inv == Cardinality(x) < 2` prints 9 states
generated, 4 distinct, none left and depth 3 in six of six runs of the Jar, the binary (and main)
7, 4, 1; `Init == x \in 0..2`, `Next == x' = 6 \div x` prints 7, 5, 0 and depth 2, the binary 3,
3, 2 and depth 1. One worker matches both. Under `-workers N` any stop past a lone expansion now
declines, "a stop several workers race to" (`StopCounts::is_raced`), where states are left on
the binary's queue, which TLC's other workers take as they race the stop, or where a state on the
trace is one that another state of its parent's level also steps to, whichever worker adds it
first being its parent in TLC's trace (`Next == (x = 0 /\ x' \in {1, 2}) \/ (x \in {1, 2} /\
x' = 3) \/ ...`). Of 20 shapes at `-workers 4`, each run six times in the Jar: the 11 with
states left on the queue (an invariant violated or failing, a next-state relation failing or
asserting, a deadlock, an action property violated, two initial states, a 20 by 20 grid) printed
up to six different outputs and main matched none of the 66 runs; the 4 whose trace goes
through a state two of a level step to printed two outputs each, main matching 1, 2, 3 and 4 of
6; the 3 with an empty queue and no such state (a dead end beside the trace, a step back to a
state found before) printed one output each, which main and the binary match, and still answer.

What TLC's workers print races the same way. A worker enqueues each new successor as it finds it
(`Worker.addElement`) and goes on evaluating, printing what the rest of the next-state relation,
the invariants of later successors and the atoms of the temporal properties print
(`Worker.doNextCheckLiveness`), while another worker takes the successor and prints as it expands
it; TLC's main thread finds the initial states before any worker starts (`ModelChecker.doInit`).
The binary, expanding one state at a time, prints in one order of many: `Next == x' \in {1, 2} /\
PrintT(x')` printed 1, 2, 1, 2, 1, 2 in 14 of 24 runs of the Jar at `-workers 4` and three other
orders in the rest; `x' \subseteq 1..2 /\ PrintT(x')` and `x' \in 0..3 /\ PrintT(<<x, x'>>)` printed
another order in each of three runs, which main printed in one order. A print is raced where the
binary's queue holds a state other than the one it expands, or the expansion enqueued a new
successor already (`Machine::is_print_raced`), and, for the atoms, which TLC evaluates as its
workers expand, wherever the graph holds more than one state. Under `-workers N` the binary
declines "prints TLC's workers may make in any order" once its workers printed a raced print and
two prints that differ (`WorkerPrints`); where every print is the same, the order doesn't show,
and the model answers (`Next == x' = x /\ PrintT("s")` from two initial states,
`[]<>(x = 2 /\ PrintT(x))` on a cycle of three, which the Jar prints the same in three runs of
three). A stop after a raced print, or with atoms that print and more than one state, declines as
a stop several workers race to: the worker that stops reports it as the others print
(`Next == x < 3 /\ x' = x + 1` with `<>(x = 3 /\ PrintT(x))` printed three outputs in three runs
of the Jar, the 3 before the deadlock, after it, and twice). A print with an empty queue before
the expansion's first new successor, as along a chain, still answers.
A level the search expands on several threads doesn't say which states two others step to, so a
stop after one past a lone expansion declines too.

#### An action property that fails on a step

`Worker.doNextCheckImplied` reports an action property that fails to evaluate through
`doNextEvalFailed`, as it does an invariant: `Evaluating action property P failed.` and the message
(2113), the trace to the successor, then the call stack of TLC's replay of the expansion with its
`CallStackTool` (`ErrorSite::ActionProperty`, `Site::ActionProperty`). That replay checks the
action properties of every step, seen or not, after the invariants of a successor it hadn't seen
(`ModelChecker.doNext`), so it fails again at the step. The replay of an invariant that failed now
checks them too, where it declined "a property TLC checks of each step" before. It declines an
action property the replay finds violated, which under -continue TLC prints, and one that doesn't
fail again. The evaluator words `[A]_e` whose A isn't a boolean as `Tool.evalAppl` does
(`Demand::SquareAction`), and the front gives a tuple subscript `<<...>>` its place, as SANY's
node does, which the call stack prints (it dropped that frame before, also in the Next and Init
contexts of `[FALSE]_<<1 \div 0>>`). Still declined: under -continue, with an ALIAS, a VIEW, a
POSTCONDITION or temporal properties, and in DFID as before.

#### A _POSSIBLE predicate the search didn't witness

Once a search completes, TLC checks `_CheckName` for each `_POSSIBLE` predicate in the
configuration's order (`Tool.checkPostConditionWithContext`): the first the search never
witnessed prints `_Counts`, the record of the counts TLC took, by name in TLC's order of strings,
and TLC reports `EC.TLC_POSSIBLE_UNWITNESSED` (2780) with the predicate's name and where its
definition's body is written, then the statistics, and exits 10 (`print_unwitnessed`). The pinned
Jar checks it before the configuration's POSTCONDITIONs, which it then neither checks nor prints
for (a probe of `Post == FALSE` beside an unwitnessed predicate reports the predicate alone). It
still declines with temporal properties, under DFID or -continue, beside a POSTCONDITION TLC
rejects, and for a predicate the configuration substitutes. A `_POSSIBLE` that lists a predicate
twice, which TLC reports as `Parsing or semantic analysis failed._POSSIBLE: semantic analysis of
generated module failed` after it checks every name, and the binary reported as `_POSSIBLE lists
AtOne more than once` (a known wrong output), now declines, "a _POSSIBLE predicate listed more than
once".

#### _Track, _Counts, _CheckName and _PrintCounts

`_Track(expr, name)`, which _Possible.tla defines by TLCSet and TLCGetOrDefault of the named
register "s:_possible", is answered in a model-checking search on one worker: it tests expr,
then counts the name once more where expr holds, or adds it with a count of none, and is TRUE.
`_Counts`, as a POSTCONDITION reads it, is the register's function in the order
`_Possible.counts` builds it, which it doesn't normalize: it merges the worker's normalized
function, its names in TLC's order of strings (the order TLC interned them), into a
`java.util.HashMap` by the names' hash codes (their fingerprints' halves xored), which puts a new
name at the head of its bucket and doubles its 16 buckets before adding a name where it holds
more than three quarters of them (`HashMap.merge`), and iterates its buckets in order. That order
shows where TLC prints `_Counts` without normalizing it, as in the messages of a failure to apply
it or compare it; PrintT normalizes it first. `_CheckName` and `_PrintCounts` apply
their TLA+ definitions to it, and a POSTCONDITION that applies them is no longer taken for one TLC
may compute as it starts. Still declined: _Track of constants, which TLC computes as it starts on
its main thread (`_Track of constants, which TLC may compute as it starts`), on several workers,
in a simulation or DFID, beside `_POSSIBLE` predicates or a spec that reads or sets registers
otherwise, of a condition that isn't a boolean (`a _Track condition that isn't a boolean`) or
fails, of a name that isn't a string (`_Track of a name that isn't a string`) or that TLC made as
it searched (which it interns only then), a bucket of eight names, `_Counts` read during the search, and a trace TLC rebuilds through it.

TLCExt's Trace has a minimum level of a state function, so a POSTCONDITION that reaches it is
no longer taken for one TLC may compute as it starts either: TLC evaluates the postcondition in a
state whose variables are all unassigned, where `TLCExt.getTrace` fails first, reported as its
Java method's failure, naming the variables in order ("In evaluating TLCExt!Trace, the state is
not completely specified yet (variable x undefined)."). A spec without variables still declines. An
ALIAS that reaches Trace, which TLC no longer computes as it starts for the same reason, is
evaluated on each state of a trace, as the model checker binds Trace to the trace's prefix
(`Tool.evalAlias`).

TLC checks the postconditions after an initial state some variable lacks a value in, too
(`ModelChecker.modelCheck`: `doInit` returns the violation `DoInitFunctor` threw), after the
report "current state is not a legal state", and exits with that report's status whatever they
give: what they print and the report of one that is false or fails follow it. A postcondition there
that reads the run's counts or registers (TLCGet), the CounterExample, `_Counts`, `_CheckName`,
`_PrintCounts` or a class TLC loads, with `_POSSIBLE` predicates or -dumpTrace, declines, "a
POSTCONDITION that reads the run after an incomplete initial state", as does an initial predicate
that prints there ("a failure with a POSTCONDITION in a spec that prints").

In a simulation, an ALIAS in a spec that reads Trace only as `Len(Trace)`, `Len(Tail(Trace))`,
`Head(Trace).v`, `Trace[1].v` or `Trace[Len(Trace)].v` of a variable v, or through definitions
without parameters (global or LET) that are just Trace, is answered: none of these reads the
field `_action` the simulator's Trace gives each state's record, nor fails printing the records.
Any other read of Trace in such a spec declines, "a simulation whose ALIAS may read TLCExt's
Trace", where the record or its domain may show (`Trace`, `Trace[1]`, `DOMAIN Trace[1]`,
`Trace[2].x` past the trace, `Trace[1].q` of a field no variable names); reads the check doesn't
follow, through an operator's parameter, a LET definition with parameters or `Tail(Tail(Trace))`,
decline with them though they read only the length or a variable.

#### A POSTCONDITION or an ALIAS that fails as TLC starts

TLC computes a 0-ary definition of constant level as it starts, swallows what fails there, and
holds the definition to evaluate where it is used (`processConstantDefns`), so it doesn't reject
such a POSTCONDITION or ALIAS as a constant. `is_computed_at_startup` evaluates the definition
within a call stack, and answers that TLC didn't compute it where the evaluation fails with TLC's
message, prints nothing, sets no register, and holds nothing `is_unsure_startup_failure` (the
check of `evaluate_failed_startup`, with every exemption that check now has) finds TLC may hold otherwise. `Post == 1 \div 0 = 1` then
reports 2405 at the end, and an ALIAS `[a |-> 1 \div 0]` its `_ALIASEvalError`. A function
constructor that fails, Assert, and a definition that prints still decline, "a POSTCONDITION TLC
may compute as it starts" or "an ALIAS TLC may compute as it starts".

#### An operator argument whose body is a literal

`Spec.lookup` gives an operator whose body is a number or a string as that literal, so Bags'
BagOfAll and TLC's SortSeq find no OpValue and fail with `TLC_MODULE_ARGUMENT_ERROR_AN` or
`TLC_MODULE_ARGUMENT_ERROR` ("should be a operator"), after the arguments are evaluated and, for
SortSeq, after its sequence is checked. The engine stops at such an application, and the
evaluator of failures words it as TLC does. A body of a number past an int or a decimal still
declines ("SortSeq of an operator TLC takes for its body's value").

#### A RECURSIVE definition without parameters

TLC evaluates a RECURSIVE definition without parameters again at each name of it in its body,
only where its evaluation reaches the name (`Tool.evalAppl`), so `A == IF TRUE THEN 1 ELSE A` is
1. The engine compiles such a name as a call of a recursive operator of no arguments, which keys
no memo table. One that recurses without end stops at the engine's depth ("recursion too deep"),
where TLC overflows its stack, and declines but where "A recursion without end" below reports
TLC's StackOverflowError. A definition naming itself without RECURSIVE still
declines ("a recursive zero-arity definition"). The trace evaluator nests each evaluation of a
definition without parameters as it does an operator's call, so one it meets confirming such a
definition at startup (`Test == R /\ PrintT(1)`) stops at its depth ("recursion too deep") and
declines, where it overflowed the process's stack before, on main too
(`recursive-nullary-printed-*` fixtures). Once a nesting goes too deep, every nesting fails at
once until the outermost one ends, so an evaluation that tries another way where the depth below
failed, as `R == <<R>>[1]` does, declines at once instead of trying again at every depth on its
way out, which grew exponentially and didn't finish. The front end's constant evaluator likewise
doesn't evaluate a set again to word a membership's or a bound's failure (`is_element`, `bind`)
where the evaluation stopped at its depth: `A == {x \in {1,2} : 1 \in A}` with `1 \in A`, or
`B == 1 \in UNION {IF B THEN {1} ELSE {2}}`, doubled its work at each level and never finished
(on main too), and now decline at once, where TLC overflows its stack: inside a filter's
predicate with the reason "a membership in a recursively defined filter too deep for the
constant evaluator, which TLC may overflow its stack on or not finish"
(`recursive-filter-membership` fixture), elsewhere "recursion too deep".

#### A recursion without end

The engine and the trace evaluator stop a recursion at a depth of their own ("recursion too
deep"), where TLC's stack overflows at a depth that depends on the JVM's stack. The engine notes
the stop where it evaluated the model, and the evaluator of failures evaluates the failure again.
Where its nesting goes too deep in a recursion that never ends, TLC overflows whatever its stack:
the innermost call is the whole body of the RECURSIVE operator it calls (`F(n) == F(n + 1)`, an
operator's arguments being lazy), or of a recursive function over Nat or Int whose argument
stays in the domain (`F[n \in Nat] == F[n + 1]`) and is ten million calls or more from
overflowing an int. Every frame around it must be one TLC evaluates in `Tool` itself: a
definition, a junction, IF, CASE, LET, a prime, a tuple, a record, a set enumeration, a function
application, or an operator of Naturals or Integers, a comparison, `\in` or `..`. A Java method
that evaluates TLA+ itself, as SortSeq's operator or TLCEval's argument, catches the error and
reports it otherwise (`MethodValue.eval`, `EvaluatingValue.eval`), so any other frame declines.
The replay must follow TLC's call stack, and the spec must not print.

- In the next-state relation, and in an invariant, a state constraint or an action constraint of
  a successor, TLC's worker catches the `StackOverflowError` as a `Throwable` and reports
  `EC.SYSTEM_STACK_OVERFLOW` with the trace to the state it was expanding, without the
  successor and without a call stack (`Worker.run`, `ModelChecker.doNextFailed`), and the
  statistics; it exits with 255. With ALIAS, POSTCONDITION, temporal properties or an atom that
  prints, it declines.
- An assumption TLC reports as `EC.SYSTEM_STACK_OVERFLOW` alone, exit 255 (`TLC.process`).
- As TLC computes the initial states, in Init, an invariant or a constraint of an initial state,
  it declines ("a recursion that overflows TLC's stack as it computes the initial states"). TLC
  reports the error, then replays the initial states with its `CallStackTool` and prints the
  call stack, which the unwinding of `StackOverflowError` normally empties: but where a `pop`
  in a `finally` overflows in turn, a frame stays. Six runs of the jar each printed `0. Line 15,
  column 9 to line 15, column 13` once for a state constraint (`stack_overflow_constraint`) and
  for `checker/errors/nonterminal_constant_recursion`, and the empty call stack otherwise; repeated jar runs of the probes of `Test == F(0) = 0`
  and its neighbours under init, invariant and property differed likewise, where those under
  next and assume never did.
- The library throws `TlaStackOverflowError` only where TLC overflows as it computes its
  constants, and declines these ("a recursion that overflows TLC's stack, in the library").
- A recursion that ends, but deeper than TLC's stack holds, is a known wrong output (on main
  too), a false "No error has been found" where TLC reports the overflow, below 3,000 nested
  calls, and below 6,000 where the constant evaluator computes it (below): the engine answers it
  as a TLC with a stack large enough would, where
  the jar at the corpus's `-Xss2m` overflows (1005, exit 255; 75 in a model). Past 3,000 nested
  recursive calls the engine stops (`MAXIMUM_RECURSION`, 20,000 before) and the run declines ("a
  recursion too deep that may end, or that TLC may report otherwise"): under `-Xss2m` the
  cheapest recursion, `G(n) == IF n = 0 THEN 0 ELSE G(n - 1)`, evaluated 2,000 calls in every
  context and overflowed at 2,500 in all but one run of 2,900 (in Init, as the JIT's frames
  differ) and at 3,000 even after 2,000 calls of `G(1500)` warmed it up, so no recursion past
  3,000 calls answers in TLC under `-Xss2m`, and main's matches there need a larger stack. A
  value the engine keeps in a table or computes once doesn't hide the calls TLC makes again:
  each kept value keeps how many recursive calls nested below its evaluation, and reading it
  counts them from where it is read (`reach_cached`), so `G(1500)` kept and then `G(4000)` stops
  as `G(4000)` alone does (`recursion-past-tlc-stack-after-cached-step` fixture); only the definitions TLC computes at startup
  (`processConstantDefns`) are read as values wherever they are. Calls of operators that call
  each other count one by one.
  The evaluator of assumptions and of failures, which answers what the engine stops on, stops at
  6,000 nested calls of RECURSIVE operators and recursive functions (its own
  `MAXIMUM_RECURSION`), on top of its bound of 10,000 nested applications of any operator: the
  corpus's `engine262` assumptions nest about 5,800 recursive calls there (they answer at a bound
  of 5,900 and decline at 5,750) and are recorded at `-Xss64m`, their `stack:` header, which the
  binary isn't told of; at `-Xss2m` the jar overflows on all three. So **known wrong**, as on
  main: a recursion of 3,000 to 6,000 nested calls in an assumption, or in a failure the
  evaluator answers, prints TLC's result under a larger stack, as `ASSUME G(4000) = 0` prints
  "No error has been found" where the jar at `-Xss2m` overflows (past 6,000 it
  declines, alone or after a value kept below: the `assumption-recursion-past-tlc-stack`
  startup fixtures). Main answers
  up to 10,000 there. The same holds in every other context for a recursion the front end's
  constant evaluator computes, a constant expression it computes as it lowers the model: with
  `G(n) == IF n = 0 THEN 0 ELSE G(n - 1) + 1`, `G(1500) = 1500` through `G(5000) = 5000` as the
  initial predicate, the next-state relation, an invariant or a property is a clean run (exit 0,
  or the statistics of one) where the jar at `-Xss2m` overflows (1005, exit 255) at every one of
  those depths; `G(10000)` declines there, as on main, which also answers `G(10000)` as an
  assumption. How deep TLC goes depends on its stack and
  on the frames each level takes, which the engine doesn't model: `f(n) == IF n = 0 THEN 0 ELSE
  f(n - 1)` answers at 2,000 and overflows at 3,000; with the call under eight nested `+` it
  overflows at 350; under six `/\` at 750; a recursive function, a LET or a filter membership
  (`A(n) == IF n = 0 THEN {1} ELSE {x \in {1, 2} : 1 \in A(n - 1)}`, `1 \in A(1500)`) at 1,500;
  `f[n \in Nat] == IF n = 0 THEN 0 ELSE f[n - 1] + 1` at 1,000 in every context, a CASE or a LET
  around the call at 1,000 to 1,500, and two operators that call each other at 1,400 levels (2,800
  calls). Even the cheapest recursion is not reliable below the bound: `G(1500)` evaluated
  three times and then `G(2000)` overflowed in an assumption, an initial predicate, an invariant
  and a property, where `G(2000)` alone evaluated. All of these answer, wrongly, as on main.
  The engine's own stack per level doesn't follow TLC's (it gave about 340 bytes a level for the
  first and 850 for the eight `+`, where TLC's ratio is about 9), so no bound of the engine's
  matches TLC's across shapes, and any bound tight enough for the eight `+` would decline the
  corpus's `engine262` runs (`print_sum`, `functions_and_arrays`, `uncaught_type_error`), which
  recurse over 1,000 levels deep and are recorded at `-Xss64m` (their `stack:` header): at
  `-Xss2m` the jar overflows on all three. The filter membership is also exponential in TLC, which
  filters a set enumeration at once at each level and so evaluates `A(n - 1)` twice, where the
  engine keeps a recursive operator's values; below its overflow TLC doesn't finish (300 to 450
  levels ran past 120 s). Where the front end's constant evaluator meets such a recursion too deep
  inside a filter's predicate, as for a constant invariant or property, the run declines ("a
  membership in a recursively defined filter too deep for the constant evaluator, which TLC may
  overflow its stack on or not finish"); main ran out of memory there. In an assumption, the
  initial predicate or a step it answers, as main does.
- A recursion the evaluator can't prove endless, such as `F(n) == F(n + 1) + 0`,
  `F(n) == IF n > 100000 THEN 0 ELSE F(n + 1)` or one through SortSeq, still declines ("a
  recursion too deep that may end, or that TLC may report otherwise"), as does a constant-level
  constraint the engine evaluates as it starts.

#### A JSON key TLC built as a set

ToJson writes a function's key that isn't a string as TLC's text of it (`getObjectNode`), which
for `{1} :> 1` is `{1}` where the store may hold that set as the interval `1..1`. A function of
one key built by `k :> v` or `[x \in S |-> e]` writes the key as `k` builds it, where TLC's text
of it is the same normalized or not; a function of several keys, or one whose value holds a
record of several fields, still declines.

#### A record compared with a function in a state

The store knows a function by its domain, not by the Java class TLC built it as, so comparing a
function over strings with one over other keys stops the engine ("record compared with a
function"). TLC fails only where the receiver of `equals` or `compareTo` is a `RecordValue` and
the other value isn't one (`RecordValue.equals`: `Attempted to check equality of record:`), which
the trace evaluator knows: the engine notes the stop where it evaluated the model, and the
evaluator of failures evaluates it again, with TLC's FingerprintException head on the record
literal, and declines where it finds no failure. Neighbours with the function on the left,
`("a" :> 1)`, empty and singleton operands, sets and memberships of both, under every context,
match the jar or decline, a set of both for the reason its sort gives. An invariant of a successor that fails
so, which TLC reports without a FingerprintException (`Evaluating invariant Inv failed.`), still
declines ("a failure TLC reports as a FingerprintException"; `record-compared-with-function`
fixture).

#### A print of a variable as its assignment built it

TLC binds a variable to the value its assignment built (`x' = e`), or to the element of the set
it enumerates (`x' \in S`, and `x' \subseteq S` as `x' \in SUBSET S`), so a Print or PrintT
later in the conjunction prints that value as built: `x' = {3, 2, 1}` prints `{1, 2, 3}` where
the state the engine holds may be the interval `1..3` an earlier action built, and prints
`1..3` where `x' = 1..3` assigned it. The walk notes, for each variable a print reads, which
assignment on its path assigned it, and a Print or PrintT that is a conjunct of the walk prints
the variable as that expression builds its value; a primed expression is built as the
expression is, and a filter of a set enumeration or an interval as the set enumeration of the
elements it keeps (`SetPredValue.toSetEnum`). A set enumeration of sets prints them alike
whatever their sizes, since the print normalizes them. A print inside a definition, a
disjunction or a quantifier, a variable a disjunction of more paths than the walk specialises
assigned, the state's own value of a variable, or a set enumeration of sets built otherwise
(`{1..2, {5}}`) still declines ("printing a value whose text depends on how TLC built it").

A print of a name a LET defines without parameters, which the LET names once and nothing
evaluates more than once (`LET f == [x \in 1..2 |-> {x}] IN LET g == f IN PrintT(g)`), prints
the value as its expression builds it: TLC computes the `LazyValue` only at that use, with the
use's `EvalControl`, as it computes the expression written in its place. So does one the LET names
more than once (`PrintT(g) /\ PrintT(<<g>>)`, `LET g == f IN PrintT(g) /\ PrintT(f)`) where no
use may evaluate it with `EvalControl.KeepLazy` (`Compiler::is_used_eagerly_in_let`): whichever
use computes the `LazyValue` builds it as written, a later use reads that value or computes it
again alike, and Print's `deepCopy` and `deepNormalize` leave the kept value as it was. A use as
the function of an application or a field's record (OPCODE_fa's `setKeepLazy`), as an argument of
an operator other than the builtins that evaluate their arguments in place
(`EAGER_ARGUMENT_BUILTINS`), or through a later definition used so, still declines: TLC's
`LazyValue.getCachedValue` ignores KeepLazy, so a function constructor first computed there is
kept as a `FcnLambdaValue` whose values `deepNormalize` doesn't reach. After `z == [b |-> 0]` has
interned b first, `LET g == [x \in 1..2 |-> [a |-> x, b |-> {x}]] IN g[1] = g[1] /\ PrintT(g)`
prints `<<[a |-> 1, b |-> {1}], ...>>` and `PrintT(g)` alone prints `<<[b |-> {1}, a |-> 1],
...>>`. main prints the fields as written in both, so it matches the shapes that apply the name
first (`g[1] = g[1] /\ PrintT(g)`, `LET h == g IN h[2] = h[2] /\ PrintT(h)`, `\E k \in {g[1]}
: PrintT(g)`) by chance and is wrong on those that print first. A function over the domain of a
tuple (`[x \in DOMAIN <<1, 2>> |-> {x}]`) is built over an interval (`TupleValue.getDomain`), as
one over `1..2` is; so is one over the domain of `\o`, Append or Tail, which build a `TupleValue`
where they don't fail. A function over the domain of a record, of `k :> v`, or of a function
constructor over a set enumeration, a map or an interval is built over that domain's keys as
they are, which `getDomain` gives whether or not TLC kept the function lazy. These declined where
main matched; a definition with parameters, and a domain of a function TLC may hold over a lazy
set (`DOMAIN [i \in SUBSET {1} |-> i]`, `DOMAIN [i \in UNION {1..2, 3..4} |-> i]`), still
decline.

A union of two set enumerations whose elements are built alike, an intersection of two such, a
difference of a set enumeration or an interval, a `UNION` of a set enumeration of set
enumerations or intervals, and a map `{e : x \in S}` print as a set enumeration of their elements
as they are built (`SetEnumValue.cup`, `cap`, `diff`, `IntervalValue.cap`, `diff`,
`UnionValue.union`, `Tool`'s `OPCODE_soa`; a lazy `SetCupValue` or `UnionValue` prints by
`toSetEnum`), so `PrintT([x \in 1..2 |-> {x} \cup {3}])` prints `<<{1, 3}, {2, 3}>>` and not
`2..3`, as main did. A union with an interval still declines: `IntervalValue.cup` and
`SetEnumValue.cup` of an empty operand give the other operand as it is, which may print as
`2..3`. So do operands whose elements are built differently (`{1..x} \cup {{1, 2}}`), whose
equal elements either operand may give.

A Print or PrintT, which normalizes what it prints and so doesn't show how many elements a set
enumeration wrote, prints more unions: an empty set enumeration written as an operand
(`{} \cup S`, `S \cup {}`), where `cup` of the empty operand gives the other as it is or a set
enumeration of its elements, which print alike unless that operand is an interval on the right;
and two sets whose elements are built alike but for how many elements the sets among them write
(`{{y} : y \in 1..x} \cup {{}}`), where the right operand is an interval only if the left is a
set enumeration written with an element, which isn't empty. An intersection whose left operand
is a set enumeration, a map or an interval keeps that operand's elements as they are
(`{{x}} \cap SUBSET {x}`), and a set enumeration of sets built alike but for their sizes, `{{1..x},
{}}`, is UNION's operand as `{{1..x}}` is. So `(1..x) \cup {}` prints `{1, 2}` and `{} \cup
(1..x)` prints `1..2`, as TLC does. Operands whose elements are built otherwise on each side
(`{(1..3) \ {x}} \cup {1..x}`, `({1..x} \cup {{5}}) \ {{5}}`, `UNION {{1..x}, {{4, 5}}}`) still
decline, where main matches: TLC takes an element both hold from the left, and which side an
element of the result came from depends on values the store, which holds a set enumeration and
an interval alike, doesn't keep. These are to win back once the store keeps how a set was built.

#### A POSTCONDITION or an ALIAS TLC doesn't find

TLC looks a POSTCONDITION up in `defns` as it collects them all, before it evaluates any, and fails
on a name it doesn't find with an unexpected exception that nests 2229
(`Spec.getPostConditionSpecs`), as it fails on one that takes arguments or is a constant: the
binary reports it so where the IR has no definition of the name, which declined "a POSTCONDITION
without a place in the source", but under DFID. It declines, "a POSTCONDITION TLC may not find",
where the name is one `defns` may hold otherwise: a builtin (an operator a Java override
implements, as `Head` with Sequences, which TLC holds as a value and rejects as a constant), a
root constant, a variable, a substitution, or TRUE, FALSE, BOOLEAN and STRING. An ALIAS that names
a builtin now declines "an ALIAS that names a constant" too, where it printed 2229 for `ALIAS Head`
(TLC prints `The alias Head cannot be a constant.`), as the base and main did.

#### A temporal formula in an action constraint, and a check of a step back to its state

`Tool#evalAppl` fails on `~>` and `-+->` (`OPCODE_leadto`, `OPCODE_arrow`) as on `[]A`, before it
evaluates the operands: the engine compiles them to the same failure, and the evaluator words
them `TLC encountered a temporal formula (a ~> b)` and `(a -+-> formula)`, where they declined
"the operator ~>" before. TLC finds the successor of a step whose check failed among the state's
successors (`Tool.getState`), so the rebuild walks the actions for a held successor equal to the
state before it, as `Next == x' = x` with a failing action constraint, which declined "a step
whose action the rebuilt trace lacks". `\EE` and `\AA` still decline.

#### An ALIAS that is a function but no record

TLC prints the state through the ALIAS's `toState`: a `FcnRcdValue` of strings converts to the
record of its sorted keys (`FcnRcdValue.toRcd`), and every other value, a function of other keys
or over an interval, a tuple or a `FcnLambdaValue`, gives none, so TLC prints the state itself
(`Value.toState`, `Tool.evalAlias`). The ALIAS answers so where the evaluator built the function
as TLC does (`java_class`); a function of strings TLC may keep lazy, such as a recursive
function's, and one of no keys decline.

#### Where an ALIAS that prints prints

TLC prints what an ALIAS prints where it evaluates the ALIAS, which isn't always where it prints
the state. A behavior's trace evaluates it on each state as it prints it (`TLCTrace.printTrace`),
so its prints come before each state. A temporal property's counterexample evaluates it on every
state before it reports the violation (`LiveWorker.printTrace`, `LiveCheck.printErrorTrace`): all
of the ALIAS's prints come, in the trace's order, after what the spec prints as TLC rebuilds the
trace and before what the property's atoms print as TLC finds the properties it violates, then
2116 and 2264. An invariant or a property an initial state violates evaluates it as TLC builds the
message (`ModelChecker.doInit`, `Simulator.simulate`), so its prints come right before 2107 or
2108, the simulator's included. The binary printed a counterexample's ALIAS prints before each
state, and dropped an initial state's and a simulation's.

Still declined: a counterexample whose states TLC rebuilds between the ALIAS's prints, where the
spec prints too, since the rebuilt trace holds what the spec printed as one ("a counterexample
whose states TLC rebuilds between the prints of an ALIAS that prints"; LiveCheck interleaves each
step's rebuild with the ALIAS on the state before it, as a lasso's cycle does, which declines
earlier as "a step back into the cycle of a spec that prints"); and a simulated behavior whose
ALIAS prints ("a simulated behavior printed through an ALIAS that prints"), which TLC evaluates
again for the postconditions' counterexample after its summary (`SimulationWorkerError.getTrace`).
Main declined each of these. The `AliasPrint*` fixtures of `trace_reports` are recorded from the
jar.

#### A subscript TLC fails to compare as it adds a state to the behavior graphs

`LNAction.eval` and `Tool#enabled` compare the two values of the subscript of `<<A>>_v` with
`v1.equals(v2)`. Where that fails as TLC adds a state to the behavior graphs, TLC's worker reruns
the atom with its `CallStackTool`, which gives the values the subscript builds (a tuple, as
`WF_<<x, y>>(A)` writes) their sources, so the comparison throws a FingerprintException
(`TupleValue.equals`). That escapes `Worker#doNextCheckLiveness`, which prints no call stack, and
`ModelChecker#doNextFailed` reports it as a general error whose message is null: TLC prints only
the trace and the statistics. The binary printed 2103 and 1000 `Attempted to check equality ...`
before the trace, as the base and main did (or declined, "an atom of the temporal properties that
may fail to evaluate"). It now prints only the trace where the replay gave the subscript's value,
or a part it compares, a source. A subscript that is a variable has none, and TLC still prints the
call stack and the message. Where the spec prints as the rerun fails, it declines, "an atom that
prints as its rerun fails as a FingerprintException". Only a failure of the subscript's own
comparison (`subscript_equals`) prints so: a failure the replay meets elsewhere in the atom that it
marks fingerprinted, such as `WF_x(Next)` with `Next == x' \in [{1} -> {1, 3}] \cup {7}` from
`x = <<0>>`, where TLC prints 2103 and 1000 `Attempted to check equality of the function <<0>>
with the value:\n7` before the trace (the membership grid's `MFunctionsCupKind`), still declines,
"a failure TLC reports as a FingerprintException".

A check of an initial state (an invariant, or a property TLC checks as one) that fails in a method
of a value its own evaluation built, such as the comparison of a function constructor over a
reducible domain whose body divides by zero, is reported as TLC reports it: the first pass's error
(1000 with the nested message, or 2102 with the state for an error that isn't an EvalException),
then 2147 with the frames its replay of the initial states froze, the initial predicate's first
(`CallStack.freeze`). `DoInitFunctor.addElement` catches the FingerprintException as a `Throwable`
and keeps it, so that replay goes on generating the initial states left, pushing the frames the
initial predicate evaluates after the failing state onto the frozen stack and counting each state
as generated, which the replay follows. Where the rest of the initial predicate fails or prints,
it declines; where TLC would print its progress over two initial states, it declines as before.

`x \in S` that assigns a variable, where S is a value that is no set (a tuple, a record, a
function, a number, a string, a boolean or a model value), fails in `Tool.getInitStatesAppl`,
`getNextStatesAppl` or `enabled` ("the right side of \IN is not enumerable") outside any of the
value's methods, so TLC prints the nested expressions, not a fingerprint stack, though the value has
a source.

#### -lncheck off

With off, `LiveCheck.finalCheck` returns at once: the search still adds each state to the behavior
graphs and stops at a tableau node that accepts every behavior, but no check of the complete graph
runs. With several workers, where TLC's workers stop at such a node depends on how they interleave
(as under the default strategy, where `-workers 4` with `[](x = 1 => [](x # 2))` already prints a
shorter trace and other counts than TLC), so `-lncheck off` with several workers and temporal
properties declines, "-lncheck off with several workers".

#### Lazy arguments, tuple patterns of recursive functions, and a lazy filter's Enumerator

`Tool.evalAppl` binds each argument of an operator as a `LazyValue`, which TLC evaluates only
where the body reads the parameter. A recursive operator's call evaluates its arguments as it
calls, but for a parameter the body never names, whose argument it never evaluates, so one that
fails or prints there is as in TLC. An argument the body may read but TLC never reaches still
stops for the evaluator of failures, which declines where it doesn't fail.

A global recursive operator with operator parameters (SANY accepts one where the RECURSIVE
declaration's last slot is plain) compiles for the operators the outermost call passes, where its
body names each operator parameter only to apply it or to pass it on, as written, to a call of the
operator itself: TLC binds each to the same operator at every depth. Any other use declines (`a
recursive higher-order operator`): TLC looks a LAMBDA's names up where it applies the LAMBDA, so
one that names a parameter and is passed to a deeper call reads that call's binding.

A recursive function over a tuple pattern, `F[<<a, b>> \in S \X T]`, binds each name to its
element of the argument once the argument is in the domain, as `FcnLambdaValue.apply` does; the
domain of a product of as many sets as the pattern names holds only such tuples. A tuple
pattern over any other set still declines (`a recursive function over a tuple pattern`).

Enumerating a filter TLC keeps lazy (`SetPredValue.Enumerator`), as `S # {}` or `Cardinality`
does, fails on an element a tuple pattern can't bind with "Attempted to check if the value: ... is
an element of a set of N-tuples." and on a predicate that isn't a boolean with "Evaluating
predicate P yielded non-Boolean value.", P as SANY's `toString` gives it (a numeral as written,
another node by its place). The membership's own wording (`SetPredValue.member`, "The evaluation
of predicate ...") still declines.

#### TLCEvalDefinition, system properties, "exit", and TLCGet of the run

`TLCEvalDefinition(name)` (`TLCExt.tlcDefByName`) evaluates the body of the root module's
definition of that name as written, in the caller's states, and fails as TLC does (2283 wrapped
in 2154) for a value that isn't a string, a name the root module doesn't define
(`ModuleNode.getOpDef`: its own, extended and instantiated definitions, `N!F` for a named
INSTANCE, not an inner module's), and a definition with parameters, by its signature. The front
end looks up each name written as a string, so a name the spec computes declines
(`TLCEvalDefinition of a name the front end didn't look up`), as does a name a standard module
defines but Nat and Int, a function's, one the configuration substitutes for or assigns, one a
Java method overrides, and one whose body has effects or warns. Nat and Int, where the jar's own
Naturals and Integers define them, evaluate to the `{ }` those modules write, which TLC evaluates
in place of the Java method, with that node's source in a FingerprintException.

TLCEvalDefinition's Java method has no minimum level, so `processConstantDefns` computes a
constant definition that applies it as TLC starts, but `tool.getSpecProcessor()` is still null
there, and TLC swallows the failure and computes the definition again wherever it is read, its
values then with sources. The evaluator of failures follows that; a constant definition that may
apply TLCEvalDefinition and print, draw or reach TLC's registers declines (`a constant definition
with effects that TLC computes again after TLCEvalDefinition fails as it starts`), as its effects
up to the failure show once more as TLC starts.

`TLCSet("-D<name>", v)` sets the system property to `v`'s text (`System.setProperty(name,
v.toString())`), which `TLCGet("-D<name>")` reads back, the key itself before. It declines with
several workers, whose threads share the property in the order they race to it, for a name the JVM
or TLC reads (`java.`, `user.`, `tlc2`, ...), and for a value whose text depends on how TLC built
it.

`TLCSet("exit", TRUE)` where TLC evaluates it as it computes the initial states or expands a state
(the next-state relation, a constraint, an invariant) stops the search as `ModelChecker.stop` does:
TLC computes every initial state, or finishes the state it expands, each successor counted and
checked, then finds the queue finished. One that runs as TLC starts still declines (`TLCSet("exit",
TRUE) as TLC starts or computes the initial states`), as does one with temporal properties, and,
outside an invariant, one with several workers, whose other threads race the stop, each finishing
the state it expands (`TLCSet("exit", TRUE) outside an invariant with several workers`). Where the
evaluator of failures replays a step, TLCSet("exit", TRUE) changes no value it computes; in an
initial state it still declines (`TLCSet of a key that stops or configures TLC`).

`TLCGet("action")` outside a simulation is the record of `Action.UNKNOWN` (`UnnamedAction`, at line
0 of `--TLA+ BUILTINS--`), since a state of the breadth-first search holds no action; printed whole,
whose fields TLC writes as built, it declines. `TLCGet("all")` with one worker is the function from each
register set to the tuple of its value. TLC builds it from a HashMap, in that map's order, but
sorts a function whose keys are all integers wherever it compares, fingerprints or writes it
(`FcnRcdValue.isTuple`, `getDomain`), so it is the function of the sorted keys. As TLC checks the assumptions its checker has found no state: TLCGet of "generated",
"distinct" and "queue" is 0, of "diameter" 1, of "all" and "all:named" the function of each
register TLCSet set so far, numbered or named, to the tuple of its value once for each worker
(TLCSet on the main thread sets every worker's, `setAllValues`, `setAllNamedValues`), the empty
function where none is set, and in a simulation's assumptions, after a TLCSet, they decline
(`TLCGet of the registers a simulation's assumption set`). A field of `TLCGet("stats")` but its duration is 0 (1 for its diameter). TLCGet("stats") read
otherwise, which holds the time TLC has run, and "revision", whose record is the jar's build, still
decline, but where nothing the spec writes, in any definition or assumption, may read the time or
the build: TLCGet("stats") only through its domain and its other fields, also through a LET's name
for it, and TLCGet("revision") only as the operand of DOMAIN (`Builtin::RUN_UNKNOWNS_UNREAD`, the
analysis a POSTCONDITION's read of the duration has). There the engine builds both records, with
the counts it keeps (one worker, no temporal properties, which read the diameter otherwise) and 0
or empty strings for what only TLC knows, which nothing shows. A definition that names
TLCGet("stats") whole anywhere, used or not, a TLCGet of a key that isn't written out, and the
record printed, compared or applied outside its domain, still decline. With one worker the search keeps the counts TLC's model checker gives as it updates
them (`DoInitFunctor.addElement`, `Worker.addElement`): "generated" counts each initial state and
each successor before its constraints, "distinct" each state as its fingerprint is put, "queue"
an initial state then and a successor once checked, less the state being expanded, and
"diameter" the level of the last state written to the trace, put with its fingerprint, at least 1
(`TLCTrace.getLevelForReporting`), so TLCGet of them, and a field of `TLCGet("stats")` but its
duration ("worker" is 0), answer in the initial predicate, a step, a constraint and an invariant.
With several workers, in a simulation, and the diameter where the search checks temporal
properties, they still decline.

Outside a POSTCONDITION TLCExt's `CounterExample` is the empty one TLC builds where none is bound
(`TLCExt.error`, `new CounterExample()`), `[action |-> {}, state |-> {}]`, and `ToTrace` of it,
written as its argument, is `<<>>`. In a spec that names CounterExample, `ToTrace` of any other
argument, as a name for it (`CE == CounterExample`, a LET), stops (`ToTrace of a value that may be
TLC's CounterExample`) for the caller's evaluator, which tells TLC's record from a plain one: an
assumption it checks, and elsewhere it declines.

`TLCCache(e, k)` of an `e` that reads nothing that varies, has no effect and holds nothing TLC keeps
lazy is `e`'s value wherever TLC first cached it, so the evaluator of failures evaluates `k`, then
`e`, and reports a failure of either as `TLCExt.tlcEval2`'s (2154); TLC never caches a failure.
Another `e` it declines (`TLCCache of an expression whose value TLC may cache otherwise`). TLC
initializes the value it caches (`value.initialize()`: `deepNormalize`, then `fingerPrint`), so a
value it can't fingerprint, as a function over Nat, fails there: the engine stops where it can't
fingerprint the value, and the evaluator declines it (`TLCCache of a value the evaluator doesn't
fingerprint`), where `main` answered as though TLC kept it. TLC hashes the key too
(`Value.hashCode`, a fingerprint), as it puts the value in the cache, and as it looks the key up
once the cache holds an entry, before it evaluates `e`: a key TLC can't fingerprint fails there,
as tlcEval2's 2154, whether or not `e` fails. The evaluator words it for a set enumeration it
can't sort (`TLCCache(1 + 1, {1, "a"})`, with `SetEnumValue.normalize`'s comparison), declines
any other key it can't fingerprint (`TLCCache of a key the evaluator doesn't fingerprint`: Nat,
STRING, `[a |-> Nat]`, `<<{1, "a"}>>`), and declines where `e` fails as well, whose failure TLC
reports only before the cache holds an entry (`TLCCache of a failing expression with a key TLC
can't hash`); it had answered as though TLC never hashed the key. TLC reads the cache as the tool
object of `e`'s node, which for a numeral or a string is the value `processConstants` gave it, so
`TLCCache(2, k)` and `TLCCache("s", k)` fail casting it to a HashMap, after `k` is evaluated, with
Java's ClassCastException in tlcEval2's 2154 (`(2)` is the numeral, `-2` an operator applied, which
caches): the engine stops (`TLCCache of a literal, whose tool object isn't a cache`) for the
evaluator, which words it, where both had answered `e`'s value. TLC computes a constant
definition as it starts and again where it is used, after swallowing its failure
(`processConstantDefns`), so what printed before a TLCCache that fails shows twice: the evaluator
declines such a failure after a print (`a TLCCache failing after a print TLC may show twice`).
TLC's `CallStackTool` replays a failure after TLC cached `e`'s value, which has no source, nor
has any value within it, so a failure of that value or of a part of it later is no
FingerprintException (`TLCCache(<<<<>>>>, 1) = <<1>>`, `TLCCache([a |-> <<>>], 1) = [a |-> 1]`);
nor is one of TLCEval's value cached for a constant argument (`tlcEvalConst`), or of any part of
it (`TLCEval(<<<<>>>>) = <<1>>`, `TLCEval({<<>>}) = {1}`, `TLCEval([x \in {1} |-> <<>>]) = [x
\in {1} |-> 1]`, where the binary printed "TLC was unable to fingerprint."), nor of the tuple or
record TLCEval makes anew of another (`convert`, `toFcnRcd`), whose parts keep their sources, which
makes a record a function, worded as one (`TLCEval([a |-> 1]) = 1` fails "Attempted to check
equality of the function [a |-> 1] with the value: 1"). `TLCFP`
of Nat, Int, Real or STRING fails as `Value.fingerPrint` does, "TLC has found a state in which the
value of a variable contains Nat", in `TLCExt.tlcFingerprint`'s 2154. `TLCEval` of a function the
engine keeps lazy stops for the evaluator of failures (`TLCEval of a function TLC keeps lazy`),
which words TLC's failure to build one over a domain it can't enumerate (`FcnLambdaValue.toFcnRcd`)
and declines where TLC builds it.

An argument of Print or PrintT that is itself a Print, a PrintT or a TLCSet runs where TLC runs it,
once, before the print it is an argument of (`Tool.evalAppl` evaluates a Java method's arguments
in order before it applies the method), so `PrintT(TLCSet(1, 0))` prints `TRUE` after setting the
register and `Print(PrintT(1), PrintT(2))` prints `1`, `2`, then `TRUE  TRUE`. Any other argument
that prints or sets a register still declines (`unsupported: Print`, `unsupported: TLCSet`).

#### DOMAIN's location, dependents past a lazy set, and TLCFP of a model value made as it runs

DOMAIN of a value that isn't a function names its own node once (`Tool`'s OPCODE_domain,
`Assert.fail(... + expr)`), and the failure passes through any DOMAIN around it unchanged. The
evaluator added the location of each DOMAIN the failure passed through (`DOMAIN DOMAIN 0 = {}`,
`D0 == DOMAIN {}` read as `DOMAIN D0`, an operator's DOMAIN applied inside another DOMAIN), a
wrong output main printed too, and printed where main declined. It now adds only the failing
node's (`domain-of-*` startup_checks fixtures).

A constant definition with no effect of its own that names one that failed as TLC started is
evaluated again as TLC computes it (`Startup::dependents`), where TLC evaluates the failed one
again with its prints. Where the engine failed on the dependent before any effect at a value TLC
builds lazily without looking at its operand, TLC goes on to the failed definition and prints
again: a union, an intersection or a difference with an operand that isn't a set
(`SetCupValue`), a filter of a value that isn't Reducible (`SetPredValue`), a product, a set of
records or of functions, UNION, a function over a non-set, or a set enumeration the engine sorts
where TLC holds it unnormalized (`UNSURE_FAILURES`, `UNSURE_COMPARISONS`,
`LAZY_OPERAND_FAILURES`). `D1 == PrintT(1) \div 0` with `<<1 \cup 1..3>> = <<D1>>` or
`<<{x \in 1 : TRUE}>> = <<D1>>` printed `1` twice where TLC prints it three times (a wrong output
main declined). These now decline ("a definition TLC computes at startup that fails there"),
as main did. A failure after an effect is inside the failed definition, which TLC fails in after
the same effects, and stands. A set of functions with an operand that isn't a set
(`[1 -> {1}]`, `[{1} -> 1]`, `SetOfFcnsValue`), which the engine checked as it built it, was
missing from that list: `<<[1 -> {1}]>> = <<D1>>` (in a tuple, a set or a union, and as a
dependent no assumption reads) printed `1` once less than TLC, as before this rule (main
declined); it declines too.

A dependent of definitions that each failed before any effect is no longer evaluated: TLC
evaluates such a definition again, where it does at all, without an effect, so it computes the
dependent without one or fails on it without one, and evaluates it again at each use as the
engine does. `D0 == Cardinality({PrintT(x) : x \in <<>>})`, which fails as `Tool.contexts`
finds `<<>>` isn't Enumerable, named in `D2 == [x \in {1, 2} |-> <<"a", D0>>] \cup {...}`, which
the engine can't compute as TLC keeps it, declined ("a definition TLC computes at startup that
fails there") where main matched; it matches again (`startup-failing-map-named-by-lazy-function`).
One the configuration names still is, as `processConfigInvariants` reads what TLC kept of it,
and declines ("a definition TLC computes at startup that fails there, named in the configuration")
only where it or a failed definition it names printed or drew as TLC computed it: the engine
evaluates it once more there, which, without an effect, shows nothing TLC doesn't.
`INVARIANT Dep` or `CONSTRAINT C` with `C == Dep` over `Dep == <<D0>> = <<D0>>` and the `D0`
above declined where main matched; these match again, as do the same with a failing quantifier
bound, `CHOOSE x \in {} : TRUE` or `1 \div 0` for `D0` and an action constraint or a property.
The same rule answers two shapes main declined, both matching the jar:
`{PrintT(x) : x \in {1}, y \in 1}` (whose second bound fails as `Tool.contexts` builds the
enumerators, before the body) named by such a lazily held dependent, and the same with `x \in TRUE`
read by `Cardinality(D2)` in an assumption.

TLC fingerprints a model value by its name's intern number (`ModelValue.fingerPrint`,
`UniqueString.tok`), which TLCFP prints and which seeds the draws of each state a worker
expands. The IR ranks texts in TLC's order, but numbers as TLC does only the texts TLC interns
first: those of the configuration's values and those it interns as it starts, up to `@`. A
model value TLCModelValue makes of another name, in a model that reaches TLCFP, RandomElement,
RandomSubset, RandomSetOfSubsets, RandomSubsetSet or TestRandomSetOfSubsets, now declines
("unsupported: TLCModelValue of a name whose number TLC fingerprints the engine doesn't know",
and "TLCModelValue of a name whose number TLC fingerprints the evaluator doesn't know" in the
evaluator of failures): `TLCFP(TLCModelValue("zz"))` printed another number than TLC (main did
too), and RandomElement in a state holding `TLCModelValue("zz")` drew another element (main
declined). TLCFP of the root module's name made a model value (`TLCModelValue("M")` in module
M) is TLC's number on main for every spec, not by chance: the IR ranks the header's `----` and
`MODULE` as one text, as TLC numbers them, which leaves the name after them, the first text of the
root module, with TLC's number, where the names after it (`EXTENDS`'s, a definition's, a
variable's) have others. It answers again where the separator and `MODULE` rank after the texts
TLC interns first (`Ir::get_root_name_rank`; the command line gives the IR the root module's name,
the spec file's), in a model that draws, if at all, only by RandomElement or RandomSubset from a
set enumeration of numbers it writes (`tlcfp-model-value-of-root-module-name`); probes of
modules M, Barq, Mv2, Zed, x04, Rr, Long_Name_7 and Abc, as PrintT, `=`, `# 0` and `% 1000`, in all
five contexts, match the jar, and so do `RandomElement({1}) = 1`, `RandomElement({1, 2}) \in {1,
2}`, an unused `Unused == RandomElement({1, 2})`, `PrintT(RandomElement({1, 2, 3}))` and
`RandomSubset(1, {1, 2})` beside it. One that draws from any other set, which may hold the model
value and which TLC orders by its number as it draws (`RandomElement({TLCModelValue("M"), 1, 2,
3})`, `RandomElement(S)` with `S == {TLCModelValue("M"), 2}`), or from an interval or a set of
strings, still declines, as on main. Other names (`"zz"`, `"Test"`, `"TLCExt"`, `"----"`, `"MODULE"`) still
decline (`tlcfp-model-value-*` fixtures). Where
TLC computes the TLCFP as it starts, as in a constant definition that prints it (`Test ==
PrintT(TLCFP(TLCModelValue("M")))`, which TLC prints as -982368331, or `"zz"`, `"Test"` or `"a"`),
the engine stops at the number there and declines with the same reason, "unsupported:
TLCModelValue of a name whose number TLC fingerprints the engine doesn't know", not the reason it
gives a definition that fails as it starts: TLC doesn't fail there, it prints the number and
checks the model (`tlcfp-model-value-printed-as-it-starts`).
`TLCFP(TLCModelValue("Test")) # 0` in module `x02` matched on main by chance too, and declines:
main's number there is `429500562`, TLC's `-1308576350` (printed with PrintT), so main is wrong on
`TLCFP(TLCModelValue("Test")) > 0`, and matched `# 0` only as neither number is zero (and
`% 2 = 0` only as both are even).

A tuple, a record or a function compared with one that isn't a set, holding a filter TLC can't
enumerate (`<<{x \in 0 : TRUE}, 1>> = [x \in {1, 2} |-> x]` in a state), declined ("a set TLC
fails to enumerate in a method the evaluator doesn't place") where main matched: neither side's
`equals` enumerates a set, so the evaluator places the failure in the methods it follows, as
before (`tuple-of-unenumerable-filter-equals-function-init`). So where either side holds a
function TLC keeps lazy (`<<{x \in 0 : TRUE}>> = <<[y \in Nat |-> y]>>`, which main matched):
`FcnLambdaValue.equals` converts it (`toFcnRcd`) and compares it as a function, as the evaluator
does, and where its domain is what fails (`[i \in {n \in Nat : n < k} |-> i]` compared even with
itself, or inside a record), that failure is placed as it converts, as TLC reports it.

#### Earlier wrong outputs

An earlier build of the native checker printed output the jar doesn't for each of these; each now
matches TLC or declines exactly.

- A record in the value of a function TLC kept lazy, printed. TLC prints its fields as written
  where the engine printed them as TLC sorts them (by when it interned each name): a LET
  definition or an operator's argument whose function constructor TLC first computed with
  `EvalControl.KeepLazy` keeps the `FcnLambdaValue` in its `LazyValue`, whose values neither
  Print's `deepNormalize` nor `toFcnRcd` normalizes, and so does a print evaluated as the function
  of an application. After `z == [b |-> 0]` has interned b first, `LET g == [x \in 1..2 |-> [a
  |-> x, b |-> x]] IN g[1] = g[1] /\ PrintT(g)` and `Op(f) == f[1] = f[1] /\ PrintT(f)` with
  `Op([x \in 1..2 |-> [a |-> x, b |-> x]])` print `<<[a |-> 1, b |-> 1], [a |-> 2, b |-> 2]>>`
  in TLC and printed `<<[b |-> 1, a |-> 1], [b |-> 2, a |-> 2]>>` natively, as main did; `(IF
  PrintT([x \in 1..2 |-> [a |-> x, b |-> x]]) THEN <<1>> ELSE <<1>>)[1]`, a CASE there,
  `<<PrintT(..)>>[1]` and an operator's argument read there printed so too, where main declined,
  and `LET Op(f) == f[1] = f[1] /\ PrintT(f) IN Op(..)` in an assumption printed the two orders
  mixed. These now decline ("printing records in a function TLC may keep lazy, evaluated as the
  function of an application"): in the engine, a print evaluated with KeepLazy whose value holds
  below itself a record of more than one field, whatever the order of its fields
  (`Machine::keeping_lazy_function_value`), and a print of a function an application read with
  KeepLazy, before, from an operator's argument or a LET definition a use may evaluate with
  KeepLazy whose constructor holds a record constructor written out of TLC's ranks of its names
  (`kept_lazy_records`, `names_argument_with_written_records`), also through another LET
  definition naming it (`LET g == [..] h == g IN h[1] = h[1] /\ PrintT(h)`, which main printed
  as the binary did), though g is named once; a print of a constructor written out again, which
  names no local name, variable, definition or register (`Op(F) /\ PrintT(F)` with F the
  constructor written twice), builds its value afresh, which TLC prints sorted, and answers as on
  main, whatever value the store shares it with (`is_built_afresh`); a print first, which TLC prints
  sorted, still answers (`LET Op(f) == PrintT(f) /\ f[1] = f[1] IN Op(..)`, main printing the
  fields as written). In the trace evaluator, a print evaluated with KeepLazy, or of a function it
  built of a constructor TLC kept lazy, holding such a record, declines, and so does one whose
  value holds, inside a function other than a tuple, a record it would print with its fields written out of TLC's
  order, which it can't tell from one TLC built and normalized: a function constructor in the
  domain of another (`DOMAIN [i \in {PrintT(..)} |-> 1]`, which TLC prints sorted), and a LET
  name passed to `\o` or SelectSeq and printed as well (`LET g == [x \in 1..2 |-> [a |-> x, b
  |-> {x}]] IN PrintT(g \o g) /\ PrintT(g)`, whose second print TLC sorts and main printed as
  written). main matched the shapes that apply the name before printing it only by chance: it
  prints an operator's argument's records as written wherever it is printed, so it is wrong on
  `LET Op(f) == PrintT(f) IN Op([x \in 1..2 |-> [a |-> x, b |-> x]])` in an assumption of a
  model, which TLC prints sorted.
- A set enumeration holding only an INSTANCE's THEOREM or ASSUME literal TLC did not initialize
  (`THEOREM A == c` with `N == INSTANCE I WITH c <- 1`, `{N!A}`), in an assumption.
  `SetEnumValue`'s enumerator returns the null element as it is, and every loop of `Tool` takes
  null for the enumeration's end (`while ((elem = Enum.nextElement()) != null)`), so TLC finds
  `\E v \in {N!A} : TRUE` false, `\A v \in {N!A} : v = 1` true, no element for CHOOSE, and an
  empty filter or set map. The evaluator bound the null element and reported a false success or
  the NullPointerException's text (main did the same for `\E`). The evaluator's quantifiers, set
  maps (`ContextEnumerator`), CHOOSE (`OPCODE_bc`) and filters (`OPCODE_sso`) now stop there;
  a larger set holding such a literal, which TLC fails to sort, declines ("an enumeration of a
  set holding an INSTANCE fact literal TLC did not initialize, with other elements"). A
  quantifier or a set map stops there only after it evaluated, checked and enumerated every bound
  (`Tool.contexts` builds the `ContextEnumerator` after all of them), so a later bound's failure
  is TLC's (`\A v \in {N!A}, w \in {1 \div 0} : FALSE` fails dividing by zero; an earlier build
  returned at the null bound, a false success). In the initial predicate, the next-state
  relation, an invariant or a property, where TLC computes such a definition again at each use
  after it failed as it started, the engine compiles a quantifier's or a set map's bound written
  as such a set enumeration as the empty set, which ends its enumeration the same way once every
  bound was evaluated, so the later bound's failure is TLC's there too, as on main (`\E v \in
  {N!A}, w \in {CHOOSE y \in {} : TRUE} : TRUE`, `{<<1>>[2]}`, `STRING` or `{1 \div 0}` as a
  later bound, the null in the middle, `{v : v \in {N!A}, w \in {1 \div 0}} = {}`). A function
  constructor's bound, whose domain TLC holds with the null, still declines there (`[v \in
  {N!A}, w \in {1 \div 0} |-> 1] = <<>>`, "the engine stopped: an INSTANCE fact literal TLC did
  not initialize"), as before. So does one whose bound is a tuple pattern over such a set, also in an
  assumption ("a tuple pattern bound to an INSTANCE fact literal TLC did not initialize"), where
  the binary printed a ClassCastException of `null` to `TupleValue` that TLC doesn't throw
  (`[<<a, b>> \in {N!A} |-> 1] = <<>>` is false in TLC; main declines). The enumerators of a set of tuples, functions or records
  (`SetOfTuplesValue`, `SetOfFcnsValue`, `SetOfRcdsValue`) take each component's first element too,
  so a component holding such a literal ends their enumeration: TLC finds `\E p \in {N!A} \X {1}
  : TRUE`, `\E f \in [{1} -> {N!A}] : TRUE` and `\E r \in [a : {N!A}] : TRUE` false and `{N!A}
  \X {1} = {}` true, where the binary and main enumerated the null as a value. Enumerating such a
  set now declines ("enumerated a set of functions, records or tuples over a set holding an
  INSTANCE fact literal TLC did not initialize"); its size, a function set over `{N!A}` as its
  domain, and one over the empty domain (`\E f \in [{} -> {N!A}] : TRUE`, `[{} -> T]` being
  `{<<>>}` whatever T is, whose Enumerator reads no range), still answer, as on main.
- An INSTANCE's substitute that draws, read more than once in one evaluation of a definition of
  the copy (`I == INSTANCE OU WITH c <- RandomElement(1..100)` with `C3 == PrintT(c) /\
  PrintT(c)`, also where nothing reads `I!C3`, also `RandomSubset`, and a substitute naming a
  definition that draws). TLC binds the substitute to a cachable `LazyValue` at each evaluation
  of the copy's `SubstInNode` (`Tool.evalImplSubstInKind`), which draws once; the binary drew at
  each read (main declined these). The front end now declines such a copy, counting a read under
  a binder twice ("an INSTANCE substitute that draws, read more than once in one evaluation of a
  definition"); one read once (`C8 == PrintT(c)`, `C4(a) == PrintT(c) /\ PrintT(a)`) still
  answers. A substitute that draws only through constant definitions TLC computes as it starts
  (`R == RandomElement(1..100)` with `c <- R`, `c <- R + 0`, `S == R + 1` with `c <- S`, `R == LET
  x == RandomElement(1..9) IN x`, `RandomSubset`) reads the value `processConstantDefns` kept at
  every read, as the engine reads the value it computed there, and answers (main matched these);
  it declines only where that computation fails after a print or a draw, which TLC evaluates again
  at the substitute's first read (`Definition::NAMED_AT_STARTUP`, "a definition TLC computes at
  startup that fails there"). A definition that reads TLC's registers or the clock, which TLC
  doesn't keep or may evaluate again where it is read, still declines with the substitute:
  `R == IF TLCGet("level") = 0 THEN RandomElement(1..99) ELSE 0`, `R == RandomElement(1..99) + 0
  * TLCGet("level")` and `R == LET r == TLCGet("level") IN RandomElement(1..99)` with `c <- R` and
  `C3`, in an assumption, printed two draws where TLC prints one (`| 73` then `| 91`, main the
  same). Among them, `R == IF TLCGet(1) = 0 THEN RandomElement(1..9) ELSE 0` with `C3` matched on
  main in an assumption only by failing on the undefined register before it drew; it declines too.
  A substitute with another effect, read so, declines alike ("an INSTANCE substitute that prints
  or sets a register, read more than once in one evaluation of a definition"): one that prints
  (`S <- PrintT(5)` with `Op == S /\ S`, `S <- [x \in {1} |-> PrintT(x)]` with `Op == S = S`,
  `S <- <<PrintT(1)>>` with `Op == S[1] /\ S[1]`, `S <- CHOOSE x \in {TRUE} : PrintT(x)`, `S <-
  Print("p", 5)` with `Cardinality({S, S}) = 1`), or sets a register (`S <- TLCSet(1, TLCGet(1)
  + 1)`), whose effect the binary had at every read and TLC has once, also through an operator
  with parameters or a definition TLC doesn't compute as it starts, which the engine evaluates
  again at each read (`P(v) == PrintT(v)` with `S <- [x \in {1} |-> P(x)]` and `Op == S = S`, or
  `S <- P(5)`, or `S <- Q(5)` with `Q(v) == P(v)`, and `Op == S /\ S`). Main printed the first
  shapes and `S <- P(5)` as the binary did and declined the others. One through a definition TLC
  computes as it starts is read as the value it kept (`constant_once`). A function constructor as the substitute
  whose body prints, applied twice (`S <- [x \in {1} |-> PrintT(x)]` with `S[1] /\ S[1]`), which
  TLC prints at each application, declines with them, as on main.
- A startup definition that prints and failed as TLC started (`D == PrintT("d") /\ 1 \div 0 =
  0`), read as a conjunct of the initial predicate or of an action before every variable is
  assigned (`Init == D /\ x = 0`, also through a LET name, an operator's argument, `\E`, `\/`,
  ENABLED, or in `Next`): TLC keeps no value of it (`setToolObject` isn't reached), so
  `getInitStatesAppl` and `getNextStatesAppl` look up its `OpDefNode` and walk its body, whose
  conjuncts' frames stay on the call stack, and the replay took it as a value, which printed the
  2103 stack without the frame of the completed `PrintT("d")` conjunct (main declined). The
  replay now walks the body of a startup definition that failed (`resolve_action`), and these
  match.

- A definition K the configuration substitutes for a declared constant (`CONSTANT J <- K`) and
  also names as an INVARIANT, a (ACTION_)CONSTRAINT, a PROPERTY, the INIT or the SPECIFICATION.
  `processConstantDefns` takes the modules in the order SANY finishes them, each one's constants
  before its definitions; the first loop over constants to meet J computes K and sets the value
  on K's node (`opDef.setToolObject`) without putting it in `defns`, and the loop over
  definitions then looks K up to that value, no OpDefNode, and leaves `defns` alone too. The
  configuration's checks then take K as an operator and evaluate its body in each state: with
  `K == FALSE` as an INVARIANT, TLC reports `Invariant K is violated by the initial state`
  (2107), a TRUE K brings no 2149 warning, and a FALSE CONSTRAINT drops the initial state
  without error. The engine (and main) computed K as it started and reported `The invariant of K
  is equal to FALSE` (2230). The front end now keeps K an operator (`is_computed_as_substitute`)
  where K is the root module's or J's module comes no later than K's; where K's module comes
  first, as K of an extended module beside J of the root module, `defns` holds K's value and
  2230 stands, as the jar shows (`er_*` probes). A K or J the front end can't place in one
  module declines (`a definition of another module the configuration names and substitutes for
  a constant, which the front end can't place in the modules' order`), as does a constant NEXT
  K TLC keeps, whose steps TLC names by the body's expression (`<TRUE line 4, col 6 to ...>`),
  which the engine's actions don't (`a constant next-state action the configuration substitutes
  for a constant`); main reported 2233 there, wrong. A module-scoped `K <- [Probe] B` beside
  the global `J <- K` reads alike, as K's body is an OpApplNode that ignores B
  (`glob_*` probes). The configuration naming J itself is not such a read: J's entry in `defns`
  is K's OpDefNode, and a constant conjunct `J` of the SPECIFICATION whose K fails (`D == 1 \div
  0 = 1`, `CONSTANT C <- D`, `Spec == C /\ Init /\ [][Next]_x`) fails as TLC computes the
  initial states, which the engine declines as before (`a constant conjunct of the specification
  that fails at startup`, `front_constants/substitute-conjunct-failing`), where taking J for a K
  had it answer that no error was found.

- A constant definition held as a filter, or a `\cup`, `\cap`, `\` or UNION TLC keeps lazy,
  whose part prints, draws or sets a register, counted, compared or printed (`S == {x \in 1..3 :
  PrintT(x)}`, `Cardinality(S) > 0`): TLC converts the one value it keeps at the first such use
  and reads the conversion from then on (`SetPredValue.convertAndCache`), where the engine built
  the set again at each use and repeated the prints and draws. It declines ("a constant
  definition TLC keeps as a lazy set whose effects it has as it first converts it"); main declined
  these too. Where only the first assumption reads such a definition, the engine leaves it to the
  trace evaluator, which converts it as TLC does (see the paragraph on startup definitions that
  draw), and `ASSUME Cardinality(S) > 0` answers. An effect written as an element of a set enumeration, a tuple or a record, in an IF's
  or a CASE's branch or as a builtin's argument (`S == {RandomElement(1..9), 70}`) TLC has once as
  it builds the value at startup, as the engine does, and answers, as main did. So does one TLC
  evaluates as it builds the value through a conjunction or a disjunction, a LET's body naming a
  definition of the LET without parameters, or an operator the definition applies, whose arguments
  it evaluates where the operator's body names them (`S == LET p == Print("e", 1) IN {p, 70}`,
  `S == {F(1), 70}` over `F(a) == Print("e", a)`), where the engine computes the definition once
  as TLC starts and reads the value it kept (`Compiler::has_deferred_effect`): these declined
  where main matched. Such a name or argument written in a filter's predicate, a map's expression
  or a function's body, or a definition of the LET with parameters, still declines. A definition
  the engine doesn't compute as TLC starts, which names one that reads a register (`S == {D}` over
  `D == PrintT("d") /\ TLCGet(1) = 1`), still declines where an effect in it is a definition's
  the engine doesn't compute at startup either: the engine builds S again at each use, and can't
  tell whether TLC kept S's value or evaluates it again at each use, as it does where D failed as
  it started. In a definition
  without parameters an operator applied by a name local to it stands for an argument, a LET's
  definition or a LAMBDA the walk meets, which it takes as written (`Sel(1..3, LAMBDA x : x > 1)`
  over `Sel(S, T(_)) == {x \in S : T(x)}` answers; with `PrintT(x)` it declines); a startup
  definition it names that reads no register is read as the value the engine computed once, with
  its effects then alone; and reading a JSON file again shows nothing. Each of these declined at
  first and answers again as on main (corpus models of the Parity jobs, such as
  `simple_lambda` and `Traceetcdraft`).
- A startup definition that fails, of a module another extends or instantiates without
  parameters (`HD == PrintT("h") /\ 1 \div 0 = 1` in HA, `EXTENDS HA`): `processConstantDefns`
  runs for every module, over `getOpDefs`, which holds the definitions the module extends, and
  `lookup` finds no value of one that failed, so TLC evaluates it again for each such module, with
  its prints. The front end lists each such lookup as a dependent of the definition itself
  (`Startup::dependents`), which the engine evaluates where the definition failed: one that fails
  again with only its prints answers; one that draws or sets a register again, or computes this
  time, declines ("a definition TLC computes at startup that fails there"), as main did.
- A set enumeration TLC can't normalize tested in a set of functions, of records or of tuples
  (`LET S == {1, "a"} IN S \in [{1} -> {1}]`), in a state: the message TLC words prints the
  element, whose `toString` fails, so the FingerprintException holds the element's source, then
  those of the values its sort compares, after the set's. The replay left out the element's. One
  whose failure is nested deeper in the element, or whose element the replay holds without a
  source (a startup definition TLC failed to compute), declines ("a membership's message that
  fails printing a set nested in the element"); main declined or was wrong there.
- A constant definition, predicate or substitute that names a name spelled as a variable of the
  spec, bound (`\A x \in S`, a filter, CHOOSE), a LET's or a parameter's: `getLevelBound` asks the
  name's `UniqueString` (`getVarLoc`), so TLC computes no such definition as it starts, takes no
  such predicate for a constant (`processConfigInvariants`, no 2149 or 2230) and reports a failing
  substitute as non-constant (2281). The configuration's checks and the substitutes' now ask the
  same level; a definition with effects or warnings, or a predicate the configuration names, of
  such a level declines ("a constant definition TLC takes for a variable's, naming a name spelled
  as a variable"), where main was wrong (`PROPERTY` of `\A x \in {1} : x = 2`, which TLC reports
  violated by the initial state, main as a constant FALSE; an `INVARIANT` that is TRUE, which
  main warned of as a constant) or declined. An invariant, a property or a constraint only the
  configuration names, without warnings, answers where TLC reads it the same either way: the
  engine computes it as it starts and goes on where that computation fails without an effect,
  which `processConstantDefns` swallows, keeping the definition TLC then checks in each state, or
  where a property or a constraint is TRUE without an effect, which holds in each state; any other
  value or an effect stops it ("a predicate TLC takes for a state's, naming a name spelled as a
  variable, whose value as a constant TLC would read otherwise"). A property's conjunct of
  constant level the constant evaluator computes TRUE is dropped, as TLC's check of the initial
  states passes it (`\A x \in {1} : x = 1 \/ PrintT(x)`). One the spec names elsewhere still
  declines: TLC evaluates it there at each use, in the next-state relation as an action, which
  takes each disjunct (`x = 1 \/ PrintT(x)` prints in each state), where main, holding its
  value, printed nothing. A predicate that sets a register declines as before ("a constant
  definition TLC computes as it starts that sets a register"), as on the base. A substitute the constant evaluator can't compute, which TLC may
  report or not, declines with that evaluator's reason, where main answered without evaluating
  it, right only where TLC's evaluation succeeded (`D == {x \in Nat : x > 3}`): with `D ==
  {x \in Nat : x > 3} \cup {1 \div 0}`, with `\cap {1 \div 0}` in its place, or with a filter
  whose predicate fails, TLC reports the substitute as non-constant (2281) where main printed the
  search's deadlock.
- A LAMBDA written in the body of a RECURSIVE operator that names something bound around it and
  is passed to a call of a RECURSIVE operator, as `Twice(f(_), n) == IF n = 0 THEN f(0) ELSE
  Twice(LAMBDA y : f(y) + 1, n - 1)`, printed a clean run in an assumption. TLC evaluates a
  LAMBDA's body, and a LET's operator's, in the context it applies it in (`OpLambdaValue.apply`,
  `Tool.getOpContext`), where the deeper call has bound the operator's parameters again: `f`
  reads the LAMBDA itself and TLC overflows its stack (exit 255), and `R(LAMBDA y : y + n, n -
  1)` reads the deepest `n`. The evaluator of assumptions binds the names where the LAMBDA is
  written, so it now declines a RECURSIVE operator with operator parameters whose body passes a
  call of a RECURSIVE operator anything but one of its own operator parameters as it is, a
  definition of the module, or a LAMBDA naming only its own parameters ("a recursive operator
  passing a recursive call an operator that names its own bindings", the
  `recursive-lambda-naming-own-parameter` startup fixture), as the engine declines the shape in
  a model ("a recursive higher-order operator"). Non-recursive operators bind as written, in TLC
  as in the evaluator, and answer; main reports a semantic error SANY doesn't.
- A string holding a lone surrogate, as `Tail("😀a")`, a JSON `\ud800` escape or `SubSeq` of a
  pair, printed U+FFFD (on main too). TLC's output is a UTF-8 `PrintStream`, whose encoder writes
  `?` for a surrogate that isn't half of a pair, in PrintT, Print, a state, an error's message or
  a trace alike. The printers now write `?` there (`java_text`), while ToString keeps the
  surrogate in the string it makes, as TLC's Java string does: `ToString(Tail("😀a")) #
  "\"?a\""`, and `{ToString(Tail("😀a")), "\"Ba\""}` sorts the surrogate after `B` (the
  `print-lone-surrogate-*` startup fixtures). The trace exploration spec still declines a lone
  surrogate in a state ("a lone surrogate in the trace exploration spec").
- A function of several arguments applied to a set enumeration TLC fails to normalize, as
  `[x \in {1}, y \in {2} |-> x][{1, "a"}]` or `[x \in Nat, y \in Nat |-> x][{1, TRUE}]`, in an
  assumption, printed `...the argument list is: {1, "a"} which does not match its formal
  parameter.` `FcnLambdaValue.apply` prints the function and then the argument (`Values.ppr(
  args.toString())`), whose `SetEnumValue.toString` normalizes it first and fails comparing
  (`Attempted to compare string "a" with non-string: 1`). The evaluator now reports that failure,
  and declines an argument holding such a set deeper ("a function's argument holding a set TLC
  fails to normalize"; the `several-argument-*-unsorted-set-argument` startup fixtures).
- PrintT or Print of `f @@ g` whose values hold two sets TLC fails to normalize, as
  `PrintT((2 :> {2, "x"}) @@ (1 :> {1, "y"}))`, reported the failure of `{1, "y"}` in every
  context, where TLC reports `{2, "x"}`'s. `CombineFcn` builds a FcnRcdValue holding the first
  function's keys first, unsorted, and `deepNormalize` walks its values in that order; the
  evaluator holds the function sorted. Printing a function of keys other than strings that TLC
  may hold out of order (not known sorted), two or more of whose values hold such a set, now
  declines ("printing a function TLC may hold out of order, two of whose values hold sets TLC
  can't normalize", the `print-combined-function-held-out-of-order` startup fixture). Uses that
  normalize the function first, as ToString, `=` and application, report the sorted order's
  failure as TLC does and answer.
- A union TLC fails to enumerate at once fails as TLC prints it (`UnionValue.toString` expands it
  by `toSetEnum`), so that a message naming it, as `Len(UNION 1)`'s or the comparison
  `Cardinality({UNION 1, 2})` normalizes with, fails with the union's own message, where the
  native formatter printed `UNION(1)`. In an assumption both now decline ("a message that prints a
  lazy set TLC fails to expand"); main still prints `UNION(1)`.
- An assumption that enumerates SUBSET S, where S is a set of functions, records or tuples with a
  part TLC can't count, such as `SUBSET ({1} \X Nat) = {}` or `\E s \in SUBSET [a : Nat] : TRUE`:
  TLC first counts S (`SubsetValue.toSetEnum` and `elementsNormalized` call `size`) and reports
  `Attempted to compute the number of elements in the overridden value Nat.`, where the evaluator
  reported the failure enumerating S. Both now match TLC; main is wrong there.
- `ASSUME Permutations(<<{1, "a"}>>) = {}`, where TLC words the wrong argument with the value's
  `toString`, which fails sorting the set: it now declines ("Permutations of a function holding a
  set TLC can't print"); main is wrong there.
- `ASSUME PrintT([{2, "a"} -> {}] = {})` prints TRUE in TLC, which never normalizes the domain of
  the empty function set there, where the native checker failed comparing the string "a" with 2.
  It now matches TLC; main declines.
- A filter of a union of sets TLC fails to enumerate, as `ASSUME PrintT({t \in ((Seq({1}) \X {})
  \cup (SUBSET Nat \X [{} -> SUBSET Nat])) : TRUE} = {})`, which prints "Attempted to compute the
  number of elements in the overridden value Nat." in TLC, where the evaluator failed on another
  part first ("Attempted to enumerate a set of the form s1 \X s2 ... \X sn"). It now matches
  TLC; main declines.
- `VIEW` naming a definition TLC computed as it started or a constant the configuration assigns
  (see the VIEW paragraph under "Known wrong outputs").
- A too-small symmetry set is named by `addToSubTwoSizedSymmetrySetList`, which joins the tokens of
  the set's syntax (`getHumanReadableImage`): `Permutations({A})` names `{A}`, a string argument
  of Print names `"sym"`, an argument `Permutations((S))` names `(S)` (the image without its
  first 13 characters and its last). The AST keeps neither parentheses nor the token an operator
  is written with, so the front end builds the image of identifiers, numbers, plain strings, set
  enumerations, tuples, records, function constructors, CHOOSE, applications, infix operators and
  `SUBSET`/`UNION`/`DOMAIN`, and takes the module's
  text between the node's first and last tokens without whitespace where it differs from that
  image only by balanced parentheses (`(1+2)*3`, `{(A)}`, `F((1))`, `SUBSET(S)`; parentheses
  around the node aren't its tokens). For any other syntax, an operator written otherwise
  (`\union`), a comment within the node, or a line that isn't ASCII, the checker declines where it
  would warn ("a too-small symmetry set written in a form TLC names by its tokens").
- `Tool.getSymmetryPerms` counts the arguments of the SYMMETRY body's node: a set enumeration's
  elements, the predicate of `{x \in S : P}` and the expression of `{e : x \in S}`. It requires
  each element of the value to be a `FcnRcdValue`, which a tuple, a record, a function TLC keeps
  lazy (over `SUBSET S`, a product, a set of functions or records, or recursive) and any
  non-function isn't, and a function constructor over set enumerations and intervals, `:>`, `@@`
  and `Permutations`'s elements are; it fails on the first kind ("The symmetry values must be
  function records."). Where it builds the group of fewer than two permutations, as for `{}` or a
  name for `Permutations({a})`, `MVPerms.permutationSubgroup` throws an IllegalArgumentException,
  whose report holds TLC's stack trace. The engine answers these where the body tells how TLC holds
  the value and its elements; it declines an element it can't tell (a function constructor over
  a declared constant, `[e \in S |-> e]`), an empty set or one of fewer than two permutations TLC
  may not hold as a set enumeration (`2..1`), and a simulation's, whose stack trace differs.
  A name for a function definition is the constructor it defines: one that names itself is always
  lazy (OPCODE_rfs), so `{f}` and `{f} \cup {}` fail as TLC fails. Where the elements are mixed or
  not told and the body names such a definition, as in `{f, a :> b}` or `Mk(f)`, the engine
  declines ("a symmetry TLC may keep lazy").
- A configuration that substitutes for the SYMMETRY definition itself (`CONSTANT Sym <- Sym2`)
  gives `getSymmetryPerms` Sym2's node, whose value and arguments it takes
  (`SpecProcessor.processConstants` puts the substitute in `defns`); the front end and the engine
  take Sym2's body likewise. One substituted in a module's scope (`Sym <-[M] Sym2`) doesn't change
  the body TLC evaluates, which stays Sym's own.
- `ModelConfig.parse` makes a model value for each new name it reads (`ModelValue.make`), and the
  32,769th fails with `EC.TLC_FEATURE_UNSUPPORTED`, exit 255, before SANY.
- `processConstantDefns` calls `initialize` on the value the configuration assigns each declared
  constant, which normalizes its sets (`ValueVec.sort`, the inner sets first) and fails where two
  elements don't compare, as an exception TLC didn't expect (exit 255), whether the constant is
  used or not: `CONSTANT N = {1, "a", m}`. The front end follows the sort on integers, strings,
  booleans, untyped and typed model values and sets, with each class's `compareTo` message. It
  declines where two constants fail (TLC's order is a Hashtable's), where a definition TLC
  computes then may print, or where the configuration substitutes for any name ("a configured
  constant TLC fails to normalize among others it computes as it starts"), and where it can't
  follow a value or word its failure: an unranked text, a string with a quote, a backslash or a
  control character, or a message whose value is longer than 60 characters, which `Values.ppr`
  may break (`CONSTANT N = {1, "<62 b's>"}`), declines "a configured constant TLC may fail to
  normalize" whether another constant fails or not.
- `TLCEval` of a function TLC keeps lazy builds it (`TLCEval.convert`, `toFcnRcd`): over `Nat`,
  `Int` or `STRING` it fails as `UserValue.size` does, as the Java method's failure, in an
  assumption; over any other domain the trace evaluator declines. The engine declines it in a
  state as before.
- The incomplete successor of an action of several names it by `Action.getName`, without its
  parameters' values (`A`, not `A(1)`).
- `processConfigInvariants` reads SANY's level of the invariant's definition, where a declared
  constant the configuration substitutes a definition for is still the declaration: `Inv == C(x')`
  with `C <- G` gets TLC's note about LevelNode.java (its `levelParams` hold C), and
  `Inv == C(x')` with `G(a) == TRUE` is rejected as TLC rejects it, where the checker found no
  error. An invariant SANY levels as a state predicate whose substitute is an action or a temporal
  formula (`CONSTANT C(_)`, `C <- G`, `Inv == C(x)` with `G(a) == x' = a`, `x' > a`,
  `[](x = a)` or `<>(x = a)`) is evaluated as `Tool.isValid` evaluates it, of the state alone, and
  matches the jar: a prime fails as on the initial state ("In evaluation, the identifier x is
  either undefined or not an operator"), and `[]` or `<>` with TLC's message 2261 ("TLC
  encountered a temporal formula"). Main is wrong on all four. The startup fixtures
  `substituted-action-invariant-successor`, `substituted-action-constraint` and
  `substituted-temporal-quantifier-enabled` hold the jar's output.
- A conjunct of the specification that names a variable is looked up to the variable's
  declaration (`processConfigSpec`), which TLC rejects as `The operator x, which equals <the
  declaration's location>, cannot be used as a spec`, also inside a LET (`Spec == LET z == 1 IN
  Init /\ x /\ ...`) and where TLC inlines an operator applied to the variable and looks its
  parameter up to the argument (`P(a) == a`, `Spec == Init /\ P(x) /\ ...`; `S(y) == Init /\ y
  /\ ...`, `Spec == S(x)`). A definition without parameters whose body names one, a global's or a
  LET's, is a state predicate TLC takes whole. A conjunct a parameter the front end still holds
  bound, or an INSTANCE's substitutions, may make a variable declines ("a conjunct of the
  specification that may name a variable through a parameter or an INSTANCE"). The expansion
  names a conjunct read through a LET's definition inside an operator (`S(y) == LET D == y IN
  Init /\ D /\ ...`, `Spec == S(x)`) by that definition, whose scope the conjunct's isn't: the
  front end finds it among the LETs of the definitions' bodies, and where it is the only LET
  definition of the name, one with parameters is looked up as above, and one without, whose body
  names the parameter, TLC takes whole, wording a failure of the conjunct (`TLC expected a boolean
  expression, but instead found 1.`) at that body, where the expansion holds the argument. A name
  two LETs define, a function, a body other than a name, or a LET definition another names (`E ==
  D`, where the expansion names the inner one and TLC words the outer's body) declines ("a
  conjunct of the specification that names a variable through a definition the front end doesn't
  find"). main answers those as TLC where the conjunct holds, and words a failure at the argument
  (`Spec == S(x)`), not where TLC does.
- `processConfigSpec` looks a LET's definition without parameters up to its `OpDefNode`, and takes
  the body whole where `getLevelBound` finds it of state level: the argument a parameter in it
  reads is not split (`S(y) == LET D == y IN Init /\ D /\ ...`, `Spec == S(x = 1 /\ x)` fails
  comparing `FALSE` with 1, where the front end split it and rejected the bare `x` as a spec; so
  did `Spec == LET D == x \in {TRUE} /\ x IN Init /\ D /\ ...`, which TLC checks). The expansion
  takes such a body whole where it reads, through the parameters, an expression the expansion
  would split, or a global definition (`Spec == S(G)`, `G == x`, worded at the LET's body `y`, not
  at G's body as main words it); a body the expansion doesn't split reads as before, and one that
  reads to a variable as the entry above says. Where the whole body fails as the engine evaluates
  it again, it declines in the engine, as main declines. Known wrong, as on main: with a constant
  argument (`Spec == S(FALSE)`, or `S(C)` with `C = FALSE`) TLC names the argument (`The spec is
  trivially false because FALSE is false.`), where the front end names the parameter (`y`): the
  front end binds the parameter to the argument's value and keeps no name of it.
- `mergeExtendContext` keeps the first declaration of a name the extended modules share, so with
  `EXTENDS FixConstant, FixVariable` the root module has a constant `Shared` and no variable.
- Within an INSTANCE's substitutions TLC splits the body of a definition the copy names without
  arguments, but the front end's copy of a parameterized INSTANCE applies it to the instance's
  parameters, which it doesn't tell from arguments written there; a temporal one in the
  specification declines ("a temporal definition a parameterized INSTANCE's specification
  applies"), as `Spec == A(x)!ALive` with `ALive == ASpec /\ WF_v(ANext)`.
- `TLCGet("stats").duration` and `TLCGet("duration")` count the seconds since TLC's class was
  loaded (`TLCGetSet.startTime`), which the JVM's start makes longer than the checker's run; a
  POSTCONDITION that may read either declines ("a postcondition that may read how long TLC
  ran"): one reaching `TLCGet` of `"stats"` other than through a field that isn't `duration` or
  through `DOMAIN`, of `"duration"`, or of anything but a literal, through its definitions and
  LETs. A name TLC doesn't find reads nothing: TLC fails looking it up (see "A POSTCONDITION or
  an ALIAS TLC doesn't find"). A read TLC never makes doesn't count: a LET definition nothing after it names, an operand
  of a junction after one that decides it, and the branch an IF doesn't take. Nor does a read
  whose result is the same for every duration, a natural (`(int) ((System.currentTimeMillis() -
  startTime) / 1000L)`): `d >= 0`, `0 <= d`, `d < 0`, `0 > d`, `d \in Nat` and `d \in Int` (and
  `\notin`), where `d` is `TLCGet("stats").duration`, `TLCGet("duration")`, or a LET's or the
  spec's name without parameters for one, and the operator and the set are the standard
  modules', which also decides a junction or an IF. So `TLCGet("stats").duration >= 0`, `< 0`,
  `\in Nat`, `LET d == TLCGet("stats").duration IN TRUE`, `PrintT(TLCGet("stats").duration >= 0)`
  and `TLCGet("stats").duration >= 0 /\ TLCGet("stats").distinct = 2` answer as TLC, as do the
same reads of `TLCGet("duration")` (the `postcondition-duration-direct` startup fixture; it
declined, "a postcondition: TLCGet", until the postcondition evaluator read that key), while
  `= 0`, `> 0`, `>= 1`, `PrintT(d)` and `[d EXCEPT ...]` decline: TLC's duration of one short
  run differs from another's (`PrintT(d)` printed 1 in the harness's runs, and `d = 0` held in a
  run by hand, the `postcondition-duration-equal` startup fixture's `jar.out`), and main, which
  reads 0, printed the harness's runs wrong.
  The front end also follows the duration as a natural it carries further, where the result is
  the same for every natural TLC computes without failing: TLC's `+` and `*` fail past
  `Integer.MAX_VALUE` (`TLC_MODULE_OVERFLOW` in `Naturals.Plus` and `Naturals.Times`), so each
  natural carries the largest value it may have for a run shorter than 2^24 seconds (194 days).
  So a sum or a product of naturals one of which reads it, no larger than `Integer.MAX_VALUE`
  (`d + 1 >= 0`, `d * 5 >= 0`), a LET operator whose parameters are of arity 0 and whose body is
  such a natural for naturals up to 2^26 as its parameters, applied to such naturals (`LET f(n)
  == d + n IN f(0) >= 0`), a quantifier over set enumerations of such naturals, whose names then
  stand for them (`\A n \in {d} : n >= 0`), a set enumeration of such naturals and number
  literals that isn't empty, or the domain of a function constructor over such sets of a bound
  name, a natural or a literal, compared with `{}` (`DOMAIN [i \in {d} |-> i] = {}`, `{d} # {}`),
  and a junction whose comparisons of such a
  natural with a number, which never fail, come before an operand that decides it, with only
  comparisons or operands that let it go on between (`d = 7 \/ TRUE`, `d = 7 /\ d = 8 /\ FALSE`;
  `postcondition-duration-carried`). The rest of what such a name reaches declines as before, as
  `\A n \in {d} : n = 0`, `LET f(n) == d + n IN f(0) = 0`, `LET f(n) == d - n IN f(0) >= 0`,
  `d = 7 /\ TRUE` and `d = 7 \/ (1 \div 0 = 1) \/ TRUE`. Declines main matches, by chance: `<
  1000`, `\div 1000 = 0`, `d >= 0 /\ d = 99`, `FALSE \/ d = 7`, `d = 7 /\ TRUE`, `d = 7 \/ (1
  \div 0 = 1) \/ TRUE` and `TLCGet(d \div 1000000) = 1` hold or fail as TLC only because the run
  took less than 1000, 99, 7 or 1,000,000 seconds; main reads 0 whatever the run took, so a run
  long enough prints otherwise. The jar shows it: with its JVM paused (SIGSTOP, then SIGCONT)
  for 5.6 seconds as it ran, `FALSE \/ TLCGet("stats").duration = 7` held, and for 96.6
  seconds `TLCGet("stats").duration >= 0 /\ TLCGet("stats").duration = 99` held, where the
  harness's runs, and main, find them false; with the model checker's `startTime` moved back
  1,000,000 seconds, `TLCGet(TLCGet("stats").duration \div 1000000) = 1` fails with `TLCGet(1)
  was undefined.` where main prints `TLCGet(0)`. Main also
  matches by chance, and the front end declines, where a sum or a product may pass
  `Integer.MAX_VALUE`: `d + 2147483647 >= 0` and `d * 2147483647 >= 0` fail in TLC once the run
  takes 1 or 2 seconds, `d * d >= 0` (`LET f(n) == n * n IN f(d) >= 0`, `\A n \in {d} : n * n >=
  0`) once it takes 46,341, `d * 128 >= 0` once it takes 2^24 and `LET f(n) == d + n IN
  f(1073741824) >= 0` once it takes 2^30, where main prints success. A string beside the duration
  in a set enumeration declines (`{d, "a"} # {}`, `DOMAIN [i \in {d, "a"} |-> i] = {}`): TLC fails
  comparing them as it normalizes the set, with a message that prints the duration, which main
  prints as 0. In a postcondition, which TLC evaluates once the search is done, three more shapes read no
  time. An argument of a parameter that an operator the spec defines (not a LET's, and with no
  substitution or Java method) never names is never computed: TLC binds it to a `LazyValue`
  (`getOpContext`). So `a >= b == FALSE` beside `TLCGet("stats").duration >= 0`, `Ign(x) ==
  TRUE` applied to it, and `F(x, y) == y` applied to it and FALSE answer, while a parameter
  named anywhere in the body, even in a branch TLC never takes (`IF TRUE THEN TRUE ELSE x`) or
  passed on to another operator, still reads it. Two reads of `TLCGet("stats")` (or of a LET's
  name for one) compared with `=`, `#` or `/=` hold the same record: the search's counts are
  final, and the duration is the same unless a second ends in the microseconds between the
  two reads, which is assumed never to happen. A LET function definition over the sets above
  with such a body, `LET f[i \in {d}] == i IN DOMAIN f = {}`, has a domain TLC builds alike for
  every duration (`FcnLambdaValue`), so its DOMAIN compared with `{}` decides as the
  constructor's does; any other use of f, as `f[d]` or `PrintT(f)`, still reads it. In other
  contexts (`TLCGet` in an invariant, where several workers may move the counts between two
  reads) these shapes are walked as before (`postcondition-duration-unread-shapes`). Declines main matches, not by chance, to win back: other shapes that carry the duration before a
  comparison that can't depend on it, as `IF d = 7 THEN TRUE ELSE TRUE`, `d = 0 => TRUE`, `\A n
  \in {d} : n = d` and `DOMAIN [i \in {d} |-> 1 \div 0] = {}`. A
  definition that only passes its parameter to `TLCGet`, as the copy
  `T!TLCGet(argument0) == TLCGet(argument0)` an INSTANCE of TLC makes (`createLocalAlias`), is
  followed as `TLCGet` of its argument, and its body isn't walked on its own; `TLCGet` or such a
  definition given as an operator's argument may be applied to anything, and declines. So
  `LET T == INSTANCE TLC IN TRUE`, `T!TLCGet("generated")` and the corpus's
  `tlc/.../test-model/EWD998/EWD998Chan.cfg` (`T!TLCSet(42, T!TLCGet("generated"))`) answer
  again, while `T!TLCGet("duration")`, `T!TLCGet("stats").duration`, a module-level
  `T == INSTANCE TLC`, `LET G(k) == T!TLCGet(k) IN G("duration")` and `Op(T!TLCGet)` decline.

- A check of an initial state that fails, or an initial predicate that fails, after a constraint,
  an invariant, a property checked as one or an implied init printed as TLC checked an earlier
  initial state (`Inv == PrintT(x) /\ (x = 1 => 1 \div 0 = 1)` with `Init == x \in 0..1`, or
  `Init == x \in 0..1 /\ (x = 1 => 1 \div 0 = 1)` with `Inv == PrintT(x)`): TLC replays the
  initial states with its `CallStackTool` for the call stack (`ModelChecker.doInit(cTool, true)`),
  and its `DoInitFunctor`, forcing the checks, evaluates the constraints of each state it finds
  before the one that fails, fingerprints it where they hold, then checks every invariant and
  implied init of it, the duplicates the first pass skipped and the states the constraints exclude
  among them, so it prints those checks' output again before the call stack. The binary printed
  only the failing state's: wrong where main declined, for a filter or another set the binary now
  prints in a state, and wrong on main alike for the plain shapes, in INVARIANT, PROPERTY and
  CONSTRAINT alike. The replay now checks each earlier state as `DoInitFunctor` does, and prints
  what those checks print, in order; one whose check doesn't hold or fails there, or whose VIEW
  prints, declines ("a check that doesn't hold as TLC replays the initial states", "a check that
  fails as TLC replays the initial states", "a VIEW that prints as TLC replays the initial
  states"), as does a replay that fails again adding an initial state to the behavior graphs
  whose target the constraints exclude or fail on ("a target the constraints exclude or fail
  on"). A replay that reports TLC's progress past two initial states still declines.
- The depth after such a failure where the initial states found before it were all outside the
  constraints (`1 states generated, 0 distinct states found`): `ModelChecker.printSummary` reports
  `ConcurrentTLCTrace.getLevel`, which is at least 1 once a state was generated, where the binary
  printed 0, as main did.
- A constraint or an invariant whose definition TLC computed as it started, as a constant
  definition with an effect (`Inv == PrintT("k")`, `C == PrintT(N)` with `CONSTANT N`), beside a
  check or an initial predicate that fails: `processConstantDefns` keeps its value in place of the
  definition, so `processConfigInvariants` and `processModelConstraints` drop it where it is TRUE
  (warning 2149 of an invariant) and no state checks it again. The replays of a failure evaluated
  its body in each state they checked, printing it again, where TLC printed it once as it
  started: wrong where main matched, for the replay of the earlier initial states, and wrong on
  main alike for the state that fails again and its successors. Each replay now takes such a check
  as holding without evaluating it, and one that failed as TLC started, which TLC keeps as an
  operator, as evaluated again in each state; a replay that wasn't told which startup definitions
  failed declines one it holds no value of ("a check TLC may have computed as it started").

- `TLCGet("config")` printed whole (`PrintT(TLCGet("config"))`, in every context): TLC's
  `install` field is the path of the jar it runs from (`AbstractChecker.createConfig`), which the
  binary, having no jar, printed as `"unknown"`; how TLC lays the record out depends on that
  path's length too. No checker can print another installation's path, so it now declines in the
  assume, init, next, invariant and property contexts ("printing TLC's install, where its jar
  is"); main prints it wrong. A field other than `install` (`TLCGet("config").mode`) prints as TLC
  does.

- `PrintT(RandomElement({[k \in SUBSET {1} |-> Print(11, k)], [k \in SUBSET {2} |-> Print(22,
  k)]}))`: at seed 4 and fingerprint index 17, TLC compares the second lazy function as the
  receiver while normalizing the enumeration and prints its 22 lines before the first function's
  11 lines, where an earlier build previewed the bodies in written order, printing 11 before 22.
  It now declines in every context ("the engine declined: unsupported: Print"), as main does
  ("unsupported: RandomElement"), until shallow normalization follows TLC's physical instances.

- A startup definition that failed and fails again where an assumption uses it no longer declines
  ("...where TLC may fail otherwise") for two shapes: a comparison in a membership (`\in`, `\notin`,
  `\subseteq`) in a set enumeration written in place there that is the only set TLC fails to
  normalize the evaluation built (`ValueVec.search` asks each element, in the order written, whether
  it `equals` the value, as the evaluator does); and a comparison failure where a lazy product or
  SUBSET is only the top of a value on the stack, not held inside another value. A lazy product or
  SUBSET held inside another value still declines: `PrintT(({1, 2} \X {3}) \ ({2, 1}))` normalizes
  the right side in `deepNormalize` before it enumerates the difference, which the evaluator doesn't
  model in general. Print and PrintT now follow `deepNormalize` itself where every value they print
  holds only sets whose Java class the evaluator knows (set enumerations, intervals, tuples, records
  and functions with comparable domains, and the operands of SUBSET, products, function and record
  sets, unions, intersections, differences and filters, in TLC's order): they report the first set
  enumeration TLC fails to normalize, before any filter is enumerated or lazy set expanded, and a
  startup definition that fails that way, or that fails expanding a union of plain sets or a set of
  tuples, records or functions or a SUBSET of plain sets after that normalization
  (`SetCupValue.toSetEnum`), no longer declines. A print that reaches `Nat`, `Int`, `Real`,
  `STRING`, `Seq`, a lambda or an overridden lazy set keeps the decline; a difference or an
  intersection whose expansion fails after normalization also keeps it, since TLC streams its left
  side through the other's membership test.

- A startup definition whose evaluation built a set map (`{e : x \in S}`) and failed comparing no
  longer declines for that alone ("...where TLC may fail otherwise: values TLC can't compare"). The
  evaluator holds a map's values as `Tool`'s OPCODE_soa does, unnormalized in the order built, and a
  membership in it asks each value whether it `equals` the one tested; the neighbours probed against
  the jar (maps of mixed, duplicate and reversed values, of sets, tuples, records and lazy sets, in
  unions, intersections, differences, products, function and record sets, SUBSET, equalities,
  memberships and prints, under every context) match. The one wrong the lift exposed was the domain
  of a record written in place, which TLC holds unnormalized (`RecordValue.getDomain` of a record
  OPCODE_rc builds with `isNorm` false), and which the evaluator now holds so: `2 \in DOMAIN [a |->
  1]` names `"a".equals(2)`, as TLC does.

- A print of a difference written as a product of written sets less a written set enumeration, as
  `PrintT(({1, 2} \X {3}) \ {2, 1})`, now words the comparison failure TLC meets as it prints it
  (`Attempted to compare the function <<1, 3>> with the value:\n2`), as the print of a difference of
  a written set of functions or records already did: `deepNormalize` normalizes the factors and the
  right side, and `SetDiffValue`'s Enumerator asks the right side of each tuple in the factors'
  order, which is the tuples' sorted order. Such a print in a startup definition that failed no
  longer declines where an assumption uses it. The right side may also be any set built afresh from
  literals, as for sets of functions and records: a union, an intersection, a difference, `UNION`, a
  set map or a filter whose predicate compares integers (`<`, `>`, `<=`, `>=`), as `PrintT(({1, 2}
  \X {3}) \ ({1} \cup {2}))`, which `deepNormalize` normalizes to the set enumeration TLC computed
  (`SetEnumValue.cup` and its siblings, and OPCODE_sso over an enumerable set, build one at once).
  One that holds sets, or is a filter TLC keeps lazy, still declines ("a startup definition the
  search found failing that the evaluator can't follow").

- `f = r` of a function or tuple `f` (`FcnRcdValue.equals`, `TupleValue.equals`) and a record, or of
  two functions one of whose domains is strings and the other's not, takes the other as the function
  it is (`toFcnRcd`: a record as the function of its fields' names, in its order) and compares the
  keys as TLC does: unequal sizes are FALSE, a key of the other against an interval fails "Attempted
  to compare an integer with non-integer", and two domains of other kinds compare key by key with
  `equals`, as `[x \in {1, 2} |-> x] = [a |-> 1, b |-> 2]` fails "Attempted to check equality of
  integer 1 with non-integer". Only a receiver whose Java class the evaluator knows is a
  `FcnRcdValue` or a `TupleValue` follows this; a `RecordValue` receiver fails on a function as
  before ("Attempted to check equality of record"), and any other declines ("record compared with a
  function"). `Seq(S)` in a comparison's message prints as `Sequences.toString` does, `Seq(` and S's
  text, where S is a set enumeration or an interval TLC prints so, as `<<1>> = Seq({1})` fails
  "Attempted to check equality of the function <<1>> with the value:\nSeq({1})".

- SubSeq, SelectSeq and SortSeq of a function TLC keeps lazy over a set it overrides (Nat, Int,
  STRING, Seq(S)) fail in their Java method's first step, `toTuple` (`FcnLambdaValue.toTuple`: "To
  convert a function of form [x \in S |-> f(x)] to a tuple, the set S must be enumerable."), after
  TLC evaluated every argument, as Append and `\o` already did. No decline remains for one over
  another set: SubSeq of such a function over `SUBSET {1}`, `1..2` or `{1, 2}` answers as TLC does.

- TLCExt's AssertEq, which TLC evaluates as its TLA+ definition, `IF a # b THEN ... ELSE a = b`,
  evaluates its arguments, which TLC passes lazily, in turn and then `#` (`equals`). A failure there
  TLC reports with the frames of TLCExt's definition, which the IR doesn't hold, except where it
  prints no call stack: in an assumption, which `checkAssumptions` evaluates with its plain `Tool`,
  and in a constant definition it swallows the failure of as it starts. There the failure is the one
  TLC reports, as `ASSUME AssertEq(1 \div 0, 1)` fails "The second argument of \div is 0.";
  elsewhere it still declines ("a failure within TLCExt's AssertEq").

- `UNION` of a set enumeration of set enumerations, written or not, now combines them at once even
  where TLC fails to normalize one of them or the set of them (`UnionValue.union` tests only that
  each is a `SetEnumValue`), testing each element against those kept with `equals`, as TLC does;
  before, the evaluator held such a union lazy. A startup definition that failed where an assumption
  uses it, whose evaluation built or used a lazy UNION, no longer declines for the union where the
  failure came before the evaluator went into the union's sets, as in normalizing the set of them
  (`Cardinality(UNION {Nat, SUBSET {1}})`, `Attempted to compare the set {{}, {1}} with the
  value:\nNat`). It still declines ("...where TLC may fail otherwise") once the evaluator enumerated
  the sets of a lazy union or tested membership in them, since it normalizes each set as it
  enumerates it where `UnionValue`'s Enumerator streams them (`{1} \cup UNION {1..3, {"a"}}` names
  `"a"` first in TLC), and in the initial predicate, a step or a property, where TLC reports a
  failure in a method of a union with a source as a FingerprintException with the union's frames. In
  a step, the evaluator words a failure in a value's method there as TLC's FingerprintException even
  past a set it holds unnormalized, but not a membership in a union of a set enumeration TLC fails
  to sort (`1 \in UNION {Nat, {2}}`, `1 \in UNION {{}, Nat}`, `LET S == {Nat, {}} IN 1 \in UNION S`,
  `1 \in (UNION {Nat, {}}) \cup {}`): `UnionValue.member` enumerates its set, which normalizes it
  and fails in the `compareTo` of the element it sorts in, so the FingerprintException holds the
  sources of the union, its set and that element, or of the `\cup` that returned the union, which
  the replay doesn't follow. Such a membership, reached through a `\cup`, `\cap`, `\` or filter too,
  and a `\subseteq` of such a union (`UNION {{0}, Nat} \subseteq {}`, one frame short), decline
  there as in the other contexts ("a set TLC leaves unnormalized", `is_unsorted_union_member`); they
  printed a stack short of frames, as on main. An equality with such a union (`(UNION {{0}, Nat}) =
  {}`, the suite's `enumerate_nat_beside_enum`) is followed. A set enumeration TLC fails to sort
  because a filter of Nat, Int, STRING or Seq(S) in it fails in its own Enumerator as it is compared
  (`SetEnumValue.compareTo` converts it, `toSetEnum`), as `{{x \in Nat : x > 1}, {}} = {}`, `# {}`,
  `\subseteq {}`, `{} \in {...}`, `\cup`, `\cap`, `\` or a LET-named filter, is placed in a step as
  main placed it, by the comparison that sorts it (the set's source, then the element the receiver
  of `compareTo`), not as an enumeration of the set the operator asks; in the initial predicate and
  the checks it declines as before. A tuple, a record or a function that holds such a set among its
  values and is compared (`<<{{x \in Nat : x > 1}, {}}>> = <<{}>>`, nested tuples, a record, `#`),
  whose `equals` compares its values in turn (`TupleValue.equals`, `RecordValue.equals`), is placed
  so too, its own source first, as main placed it in a step (26 next-state runs at 1 and 4 workers
  match).

- The decline of a comparison failure in a startup definition where a lazy product or SUBSET is held
  in another value now applies only where the evaluator also failed to sort what a lazy
  intersection, union or difference enumerates (`sorted_combination`): TLC streams those
  (`SetCupValue`'s Enumerator and the like) and may decide before it meets the incomparable
  elements, as in `({x \in 1..3 : x > 1} \cup SUBSET {1}) \subseteq {7 : y \in 1..2}`, which TLC
  finds false at its first element. A set enumeration holding a SUBSET it fails to normalize, as
  `Cardinality({Nat, SUBSET {1}})`, words TLC's failure (`SetEnumValue.normalize`, the SUBSET
  converted as it is compared).
- An EXCEPT of a function TLC keeps lazy whose domain's membership test prints, as a filter whose
  predicate does (`[[v \in {v \in Nat : PrintT(v)} |-> v] EXCEPT ![2] = 5][3]`): TLC's
  `FcnLambdaValue.select` tests the key once and evaluates the body at it, where the trace
  evaluator tested it a second time as it applied the function for `@`, printing again. That
  showed in an assumption reading a startup definition left to the trace evaluator, where main
  declined. The EXCEPT now evaluates the body at a key it tested without testing it again
  (`except-lazy-domain-tests-key-once`).
- A print of a set of functions over ANY (see "Known wrong outputs" for the membership in one).
  `PrintT([{Any} -> {1,2}])` prints
  `{(ANY :> 1), (ANY :> 2)}` in TLC, which writes the expansion in the order it builds it, and failed
  natively comparing ANY with itself as it sorted the expansion. PrintT, Print and ToString of a
  value that holds a set of functions, of records or of tuples that expands into two elements or
  more, one of whose component sets holds ANY (`{Any} \X {1,2}`, `[a : {Any}, b : {1,2}]`, and such
  a set inside a tuple, a set or a union), decline in every context ("printing a set of functions,
  records or tuples over ANY, which TLC expands as it builds it"), as main declined them
  (`unsupported: Any`). A set that expands into one element (`[{Any} -> {1}]`, `[{1,2} -> {Any}]`)
  prints as TLC does.
- A failure in a method of a value with a source, which the replay placed as TLC's
  FingerprintException, no longer declines in the initial predicate, an invariant or a property for
  a set TLC holds unnormalized that the replay built, as it didn't in a step, where the replay found
  no state TLC fails to fingerprint or print (`{1, "a"} = {1}`, `(UNION {{0}, Nat}) = {}`, `"a" \in
  {1, "a"} \cap Nat`). One TLC reports with the nested expressions alone (`UNION {{1}, {"a"}} # {}`,
  `IsFiniteSet(UNION {{1}, Nat})`), and one past a membership in a union of a set TLC fails to sort,
  still declines there, as the replay may miss a source TLC gives (a function constructor over such
  a set, `[x \in {1, "a"} |-> x] = <<>>`, is one).
- `Init == x = (DOMAIN <<1>> = TRUE)`: TLC reports a state it fails to fingerprint, with the
  value's frames and the reason, where the binary reported the failure with nested frames. It now
  matches the jar; main is still wrong.
- `1 \in Int \cup {"none"}`: TLC tests the enumerable side first and stops with "Attempted to
  check equality of string "none" with non-string:\n1", where the engine found it true. It now
  matches the jar in an assumption, an initial predicate, a step, an invariant and a property, as
  main does.
- Of the failures named otherwise than TLC names them in a union, an equality of sets or a
  membership in a UNION (the table under "Known wrong outputs"): `AssertError("Attempted to check
  equality of integer 2 with non-integer:\n\"a\"", 1 \in {2, 1} \cup {"a"})` (TRUE, as TLC),
  `{3, 1, 2} = {1, "a"}`, `Cardinality(UNION {{2, 1}, {"a"}})` and `{1} \cup UNION {1..2, {"a"}} =
  {}` (and its Cardinality) now match the jar in every context, and the record one with
  `CONSTANT mv = mv` in an assumption, where main declined; `1 \in UNION {{"a"}, {2}}` and `({2, 3} \cup SUBSET {1}) \subseteq {7}` match in an
  assumption and decline elsewhere ("values TLC can't compare"), and `x' = IF {1, "a"} \in {x}
  THEN 1 ELSE 2` declines alike.

#### Known wrong outputs

An EXCEPT of a function constructor over a set of strings a constant definition names, applied
to a number (`S == {"b", "a"}`, `[[x \in S |-> x] EXCEPT !["a"] = 2][1]`), fails comparing the
number with the domain's first element (`Attempted to compare integer 1 with non-integer: "b"`)
where TLC first compares the EXCEPT's key with it (`FcnLambdaValue.select` checks the excepts
before the domain: `Attempted to check equality of string "a" with non-string: 1`), in all five
contexts, as main does.

A constant definition that prints, draws or sets a register and reads or writes a JSON file
(`JsonDeserialize`, `JsonSerialize` and their ndJson kin), which TLC computes once as it starts
and the engine evaluates where it is used, as main does: used more than once (`T ==
PrintT(JsonDeserialize("f.json"))` with `Test == T /\ T`, `\A i \in 1..3 : T`, or `IF T THEN T
ELSE FALSE`), the binary prints at each use where TLC prints once. main prints the same. Used
once, both print as TLC does. One that converts a value (`ToJson`, `ToJsonArray`, `ToJsonObject`)
declines (see the startup definitions above).

A recursion that ends deeper than TLC's stack holds at `-Xss2m` is a false clean run, as on main,
below 3,000 nested calls, and below 6,000 where the front end's constant evaluator computes it or
in an assumption (`G(n) == IF n = 0 THEN 0 ELSE G(n - 1) + 1` and `G(3000) = 3000`: TLC reports a
StackOverflowError, 1005, exit 255); see "A recursion without end".

An interval a node that gives values a source returned (DOMAIN of a tuple or of a function over
an interval, `{} \cup (1..2)`), which the replay holds without an address, has no source where it
fails in another value's method or is read through a LET's or another definition's name, as
`LET D == DOMAIN <<1, 2>> IN D = 1` or `(DOMAIN <<1, 2>> \cup {"a"}) = {}` in a state: TLC reports
a FingerprintException with the node's source, where the binary reports the nested expressions.
main reports the same, and more such intervals besides.

`TLCGet("spec")` printed in an assumption (`PrintT(TLCGet("spec"))`): TLC, which checks the
assumptions before it builds the spec's actions, prints `actions |-> {}`, where the binary prints
the set holding the record of TLC's unnamed action (`UnnamedAction` at `--TLA+ BUILTINS--`) it
gives in a state. In an initial predicate, a step, an invariant or a property it prints as TLC
does. main is wrong there too.

A Java method given an argument that holds a set enumeration TLC can't normalize, in an
assumption, where TLC words the wrong argument with the value's `toString`, which fails sorting
the set, so that TLC reports that comparison (`Attempted to compare string "a" with non-string:
1`, or `integer 1 with non-integer: TRUE`) as the method's failure: `TLCSet({1, "a"}, 1)` (also
of `<<{1, "a"}>>`, `{{1}, {"a"}}` and `{TRUE, 1}`), `TLCGet(<<{1, "a"}>>)`, `SetToBag(<<{1,
"a"}>>)`, `BagCardinality`, `CopiesIn`, `BagIn` and `BagUnion` of `<<{1, "a"}>>`, `<<{1, "a"}>>
(+) SetToBag({1})`, `SetToBag({1}) (-) {1, "a"}` (and of `{{1}, {"a"}}` and `{TRUE, 1}`), `{1,
"a"} \sqsubseteq SetToBag({1})` and `TLCModelValue(<<{1, "a"}>>)`.
The binary reports the method's own type error naming the value (2169, 2176, 2283). So does a
comparison of `Seq(S)` for such an S (`Seq({1, "a"}) = {}`), where TLC fails sorting S as it
prints `Seq(S)` and the binary reports `UserValue.compareTo`'s failure. In an invariant these
decline. main is wrong there too.

A function constructor over a set enumeration TLC can't sort comparing scalars (`{1, "a"}`), as
the body of another function in a step (`[x \in {1} |-> [w \in {1, "a"} |-> 1]] = <<>>` and
`[x \in {1} |-> [z \in {1}, w \in {1, "a"} |-> 1]] = <<>>` under next): TLC's fingerprint stack
ends with the set's own source, which `SetEnumValue.size` adds (`FingerprintException.getNewHead`),
where the binary's stack stops at the inner constructor. main is wrong there too. The binary now
declines these ("a set TLC leaves unnormalized"; main declines them in an initial predicate, an
invariant and a property; for a step, see below): it follows a failure over a set enumeration TLC can't
sort only where its frames end at that set enumeration, or at the element of it whose own method
failed as TLC sorted it (`{("a" :> 1), <<2>>} = {}`), or at a tuple or a record that element
builds of tuples and records alone, whose components `TupleValue.equals` and `RecordValue.equals`
compare in turn (`<<<<1>>, 1>> \notin {<<<<1>>, 2>>, <<[a |-> 1], 3>>}`, ending at `[a |-> 1]`,
which answered before and matches the jar), not at a value holding it whose method fails, whose sets' frames TLC adds and the replay doesn't keep. That is a constructor, SUBSET or
UNION (`1 \in SUBSET {1, "a"}`, `1 \in SUBSET SUBSET {1, "a"}`, `1 \in UNION {SUBSET {1,
"a"}}`), a function set on either side (`1 \in [{1} -> {1, "a"}]`, `<<1>> \in [{1, "a"} ->
{1}]`, `[{1, "a"} -> {1}] \subseteq {}`, `1 \in [{1} -> SUBSET {1, "a"}]`, `1 \in [{1} -> {1,
<<1>>}]`, whose frames end at the tuple), a record set (`1 \in [r : {1, "a"}]`, `[a : {1, "a"}, b
: {1}]`), a product (`1 \in {1, "a"} \X {1}`), a filter, a union or a difference of those, and
these under a LET, an operator's argument (`LET F(S) == [S -> {1}] IN 1 \in F({1, "a"})`) or a
function's value (`1 \in [x \in {1} |-> [r : {1, "a"}]][1]`). The binary printed the stack one or
two frames short in an initial predicate, an invariant and a property too (main declined there).
In a step it declines only a failure that sorts the set where the frames end at one of those
holders (a constructor, a function set, a record set, a product, a filter, a set map, SUBSET or
UNION; `1 \in [{1} -> {1, <<1>>}]` printed one frame short where main declined); a failure of
the holding value's own method that doesn't sort the set (`1 \in [{} -> {1, "a"}]`, whose stack
ends at the function set, as TLC's does), and frames that end at another operator TLC returns the
set from (`({} \cup {1, "a"}) = {}`), still answer, as on main. A union, an intersection, a
difference or UNION one of whose sets is a function set, a record set or a product over such a set
enumeration is no such operator: in a step, `1 \in ({} \cup [{1} -> {1, "a"}])` (also `{2} \cup`,
`\cup {}` on the right, `\ {}`, `[a : {1, "a"}]`, `{1, "a"} \X {1}`, `[{1, "a"} -> {1}]`, `{} \cup
{} \cup`, `UNION {[{1} -> {1, "a"}]}`) printed TLC's sort failure ("Attempted to compare string
"a" with non-string: 1") with four of TLC's five frames, missing the set enumeration's, which
TLC's FingerprintException holds from the holder's enumeration, where main prints another
failure, "Attempted to check if 1 which is not a TLC function value, is in the set of
functions", with frames of its own. These decline in a step ("a FingerprintException through a
set a union's operand holds", `ends_at_operator_over_holder`, `is_unsorted_held_member`).

Membership in `Seq(S)` where S isn't a set of sequences' elements TLC can test (`<<1>> \in
Seq(SUBSET Nat)`, `<<1>> \in Seq(<<>>)`, `<<1>> \in Seq([a |-> 1])`) in an initial predicate, a
step, an invariant or a property: TLC reports it as a state it fails to fingerprint, with the
failure as the report's Reason, where the binary reports an evaluation failure (2103) with its
stack. In an assumption it prints as TLC does. main is wrong there too.

A constant definition TLC computes as it starts (`processConstantDefns`) that prints and then fails,
whose body holds an INSTANCE in a LET of a module with parameters that extends TLC (`Test == LET I
== INSTANCE fy WITH N <- 3 IN PrintT(1) /\ PrintT(1 + "a")`, also through an operator, `Test ==
Op(1)`), prints once, where TLC prints at startup and again where it is read. TLC's
`getLevelBound` of the LET takes the bodies of its definitions, among them TLC's own `TLCGet` and
`TLCSet` (CHOOSE bodies, constant), which the INSTANCE shares; the front end's names for them
apply the builtins, which it takes for state level, so it doesn't compute the definition as TLC
starts. main declines these only where it can't word the failure; a print before a failure the
binary words is wrong on the base too. To fix it: level a LET's name for a definition an INSTANCE
shares (not copies) by that definition's body.

An action of the next-state relation that applies an operator TLC's Java code overrides, such as
`x > 5` in `Next == x > 5 \/ x' = x + 1`, is named after that operator in TLC's report of a
successor the action leaves incomplete (`2109 ... by action > of the next-state relation`,
`<> line ...>` in the trace: `getActionsAppl` names the action by the operator node it doesn't
find an OpDefNode for), where the binary names the action after the definition that holds it.
After that report TLC also prints the failure of evaluating the other disjunct, which the binary
doesn't. main reports the same.

A module-scoped substitute for an action of an instancee read through a LET's INSTANCE
(`Step <- [M] MyStep`, `Next == LET K == INSTANCE M IN K!Step`) names the action after the copy,
`<K!Step ...>`, where TLC's `lookup` reads through the copy's `SubstInNode` to the substitute and
names it `<MyStep ...>`; through an INSTANCE with parameters (`J(z) == INSTANCE M WITH y <- z`,
`Next == J(y)!Step`) TLC applies the substitute, which has no parameters, to the copy's argument
and fails with an ArrayIndexOutOfBoundsException, where the binary steps through MyStep. main
reports the same for both. Through a named INSTANCE without parameters (`I == INSTANCE M`,
`Next == I!Step`, alone or in a disjunction) the copy is no action of the instance's: it splits
as the substitute, named after it and with no frame of the application, as TLC does.

A module-scoped substitution read through an INSTANCE's copy (`Z <- [Inn] Y`, `Y == {1}`,
`I == INSTANCE Inn`, `"a" \in I!Z`) reads Y's startup value, which compares, where TLC evaluates
Y's body as written and checks equality. main reports the same.

A module-scoped value of a standard module's definition that has no Java method, as
`SubBag = [Bags] {}` with `SubBag([a |-> 1]) = {}`, isn't read through the body, so the
invariant is FALSE where TLC reads `{}` and warns that it is a TRUE constant. main reports the
same.

A successor TLC fails to fingerprint (`y' = {1} \cup Nat`, `y' = {1} \cup 2`, `y' = Int \cup
{1}`, `y' = {1} \cup SUBSET Nat`) TLC prints the trace to by finding it again among the successors
of the state before it (`Tool.getState(TLCState, TLCState)`), comparing each with `equals`. A
failure there with a code, as the overflow of a power set's count (2178), escapes and TLC reports
it again, which the binary prints; one `Assert.fail` raises with a text alone TLC skips the
successor for (`catch (TLCRuntimeException e) { continue; }`), so it finds none, and fails
printing a trace of two states with a NullPointerException (`currentStateInfo` is null) or
reports a longer one's last state as one it failed to recover (2123, "TLC bug(5)", 2216, exit 1).
The binary repeated the first failure there. It now prints TLC's NullPointerException where
the trace has two states, the successor of an initial state, and the failure is the union's own
(`Attempted to enumerate S \cup T`, as in Spectacle's `semantic_error1`, which
`known-differences.json` no longer lists), and declines a longer trace and a failure inside a set the union holds
(`{1} \cup [a : Nat]`, `{1} \cup SUBSET Nat`), whose Fingerprint Stack Trace TLC builds from more
sources than the replay places ("a successor TLC fails to fingerprint with an error it skips
finding it again"). The shapes of a finite union of a
value that isn't a set (`{1} \cup 2`, `<<{1} \cup 2>>`, `[a |-> {1} \cup 2]`) were wrong on main
too; those of an infinite set main declined.

An ALIAS record with a field for each variable TLC fingerprints as it prints a state whose alias
has no fingerprint yet (`TLCStateInfo.fingerPrint`): each state after the first, and the first of
a trace of two, which TLC prints from the states it holds (`TLCTrace.printTrace`). It fingerprints
the state of the fields named as the variables (`RecordValue.toState`), and none where a variable
has no field (`PrintTLCState.allAssigned`). Where such a field holds a function TLC keeps lazy over
a domain it can't count (`[x |-> [i \in Nat |-> i + x], y |-> y]`), a set the evaluator doesn't
know to be finite (Nat, `SUBSET Nat`, `{i \in Nat : i < 3}`, `[Nat -> {1}]`, STRING, `<<y,
Nat>>`), a lazy union (`UNION {{1}, SUBSET {2}}`), or one whose fingerprint fails (`SUBSET
(1..40)`, `{1} \cup SUBSET {2}`), the fingerprint fails, and TLC reports the exception in place of
the rest of the trace. The binary printed the whole trace, as main does; it now declines ("an
ALIAS whose state of the variables TLC may fail to fingerprint as it prints it"). Such values in
other fields, or in a record that lacks a variable, print as TLC does (`[x |-> Nat]` with
variables x and y, `[x |-> x, y |-> y, z |-> Nat]`, the plain-lazy fixture). An ALIAS `[x |->
x, y |-> [s \in SUBSET Nat |-> 1]]` violated by the initial state, which TLC prints with
`<expression 1>` for the body, the binary now prints as TLC does; main prints the body's
location there.

An incomplete successor of an action an INSTANCE of an inner module exports, without explicit
substitutions, is labeled at the INSTANCE (`<I!A(1) line 16, col 1 to line 16, col 19 ...>`)
where TLC labels it at the definition in the inner module; main does the same.

A next-state mistyped membership whose kind-error formatting normalizes a nested mixed
SetEnum could report the right comparison but omit that SetEnum expression's final frame from
TLC's fingerprint stack, as `1 \in SUBSET {1, "a"}` in Next, as main does. Captured values do not
retain the source-expression preimage needed for that stack frame, so the replay now declines it
in a step too, as in an initial predicate, an invariant or a property ("a set TLC leaves
unnormalized", above).
Where the failure is instead the one TLC meets as it words a comparison failure with the
`toString` of the values it names (`0 = {1, "a"}`, `0 = {<<1>>, [a |-> 1]}`, `SUBSET {1, "a"} = 1`,
`({1, "a"} \X {2}) = 1`), the evaluator now reports that normalization failure, as TLC does, in an
assumption and in an initial predicate, and declines it where TLC prints a fingerprint stack ("a set
TLC fails to normalize as it words a failure, in a fingerprint stack"), whose frame of the set it
can't place. A named value that holds such a set deeper declines ("equality of values TLC can't
compare"). The `0 \in {1, "a"} \cup {2}` and `{1, "a"} \cup {2} = 0` neighbors in Next now match
TLC; main printed an extra frame of `{2}` there.

Function-set formatting also has preexisting domain-array identity mismatches. In
`1 \in [{Any} -> {1,2}]`, Java expands the receiver as `{(ANY :> 1), (ANY :> 2)}`;
native formatting retains `[{ANY} -> {1, 2}]`. A failure report the trace evaluator words (the
initial predicate, the next-state relation, an invariant or a property) declines where it prints
a set of functions, of records or a product small enough for TLC to expand that the evaluator
fails to enumerate ("a message that prints a lazy set TLC fails to expand"), as main declined
these (`unsupported: Any`); the assumption's message declines alike ("a message that prints a
lazy set TLC fails to expand"), where main prints `[{ANY} -> {1, 2}]`. With `SUBSET {Any}` as the
domain (`1 \in [SUBSET {Any} -> {1,2}]`), Java instead compares ANY with itself and fails; that
declines in every context with the same reason, where main's assumption emits a non-function
kind error. A function-valued domain key such as `("b" :> {2,"b"} @@ "a" :> {1,"a"})`
likewise needs the actual shared array: Java skips comparing that key and then formats it
in written order. Native mathematical enumeration cannot establish that observation.
These wrong answers occur on main too, at both worker counts.

With consecutive assumptions `1 \in {1, "a"}`, `[e \in {1, "a"} |-> e][1] = 1`,
and `"a" \in {1, "a"}`, TLC applies the function it keeps lazy pointwise, asking the set
enumeration it holds unnormalized for the argument element by element (`SetEnumValue.member`),
and fails on the third assumption comparing the integer with the string. The engine builds the
function, sorting its mixed domain, and fails on the second assumption. The failure's replay
applies the function as TLC does, so the check declines (`evaluating the assumption again: it
didn't fail`), and `[e \in {1, "a"} |-> e]["a"] = "a"` alone matches TLC's equality failure.
The replay applies the function in place or through a LET's name for it, which TLC keeps lazy
too (`LazyValue`); at a key outside the domain, the message's `FcnLambdaValue.toString` fails
on the sort, before it evaluates the body anywhere, and `FcnParams.toString` sorts the domain
again from the order the first sort left it in, so the failure is TLC's where both sorts fail
at the same comparison, and declines otherwise. Where the replay applies it otherwise (a body
with effects, several bounds, or outside the startup), it declines `a function TLC keeps lazy
over a set enumeration it can't sort` instead of failing on the sort; the engine and the replay still fail
on the sort in the initial predicate, the next-state relation and the checks, which decline as
`a set TLC leaves unnormalized`.

The engine stops at an EXCEPT of a record at a key that isn't a string, or of a tuple at a key that
isn't an integer, and at a comparison or an IsABag of a function TLC keeps lazy, as at a limit the
evaluator of failures follows: it words TLC's failure (`Value.select`'s "Attempted to access
record by a non-string argument", `FcnLambdaValue.toFcnRcd`'s "Attempted to compute the number of
elements in the overridden value Nat."), or declines where TLC doesn't fail. An EXCEPT's
`select` of its path throws a failure on with the source of the value it selects in, which is the
one it evaluated until a `takeExcept` builds a new one, which has none, and with the source of the
record or tuple whose `select` failed further down the path (`[[a |-> <<1>>] EXCEPT !.a.b = 0]`);
an EXCEPT on a part of the path that isn't a function after an earlier update
(`[[a |-> <<1>>] EXCEPT !.a = 5, !.a.b = 0]`), wrong on main, now prints TLC's nested expressions.
DOMAIN of a function TLC keeps lazy of several parameters is a new set of tuples of their domains
(`FcnLambdaValue.getDomain`), and the enumerator of a set of functions converts a lazy domain
(`toSetEnum`, `elements`), which may fail as it is built, with the domain's sources after the set's
(`CHOOSE f \in [(Nat \ {0}) -> STRING] : TRUE`, Toolbox's `_TETrace`).

A late native decline puts back the files the spec's operators wrote (Json's and IOUtils's) and
`-dump`'s file, which the journal keeps before the run writes them ("What a decline leaves"):
`JsonSerialize("out.json", <<0>>)` in Init followed by an unbounded CHOOSE in Next, which
declines as it rebuilds the trace, leaves a preexisting `out.json` as it was, under a
breadth-first search and under DFID. The `-dump` file, which the binary opens as it reads its
options, is kept in the run's journal before it is opened (`keep_file`), so `-dump dump.dump` on
that spec puts back the user's file, or removes the one it made, under a breadth-first search, and
so does DFID with `-dump dump.dump`, which declines later (`DFID with effects, liveness,
continuation, or output files`, `DFID with random draws, register writes, or JSON files`), as
main, which declined -dfid before it opened any file, left it. The journal keeps a file it can
read whole of at most 64 MiB, which it reads into memory; one it can't read (write-only) or a
larger one a run without -dfid truncates and writes as TLC does, and leaves what the run wrote
before a later decline, as main did, and a -dfid run declines before it opens it ("-dfid with
-dump into a file it can't keep"). The decline still leaves the other files the binary writes for
its own options, which the journal doesn't keep. `-userFile`'s, which it creates or empties as it
reads the options and to which it appends each Print, holds what the run printed before the
decline (`"hi"` where that Init also prints it), and the files `-dumpTrace` and `-teSpecOutDir`
write after a violation stay written where a later one of them can't be written and the run
declines (`-dumpTrace into a file it can't write`). `main` leaves `-dump`'s file and the JSON file
changed too.

A default `tlc2.overrides.TLCOverrides` index can replace `TLC!Any` with a method
annotated `@TLAPlusOperator(identifier="Any", module="TLC", warn=false)` that returns
`IntValue.gen(7)`. With `EXTENDS TLC` and `Test == 1 \in Any`, the pinned Jar fails with
"is an element of the integer 7", under `ASSUME Test` (exit 10) and in the configured
Init/Next/invariant model (exit 75). The front end now reads the index (see "Java overrides
that stay declined") and declines both, `TLC!Any` being a target the model evaluates; main
was wrong on the first and declined the second. The same target with
`CONSTANT Any = [TLC] {2}` also declines, where the Jar observes the indexed
integer 7. The same method annotated for `Naturals`, which has no `Any`, replaces nothing,
and the model is checked natively.

The complete pinned-Jar capture and fresh neighboring probes identify the differences below.

`TLCEval` of an interval of more than 16,777,216 elements remains compact in the trace
evaluator. If its physical set representation is observed, such as by `PrintT`, the evaluator
prints an interval where TLC prints an enumerated set. Smaller intervals are converted. This
preserves compact uses such as `Cardinality(TLCEval(1..16777217))`, which TLC and the checker
both answer correctly, until a compact representation of TLC's enumerated class is available.

An explicit Java classpath can supply a malformed `Strings.class` outside the model resolver's
lookup paths. With an unassigned root constant, TLC then reports the class-loading error
(2173, exit 255) before checking that constant. The native legacy path can instead report the
missing constant (2222, exit 151), as main does. The new origin proof treats this classpath as
opaque; it does not establish the absence of that earlier class-loading error.

Indexed Java overrides whose effective targets the front end did not resolve gave wrong answers:
a replacement of `Aux!Make == 1` returning `TRUE` under `\A i \in {1} : Make` in an invariant
reported a non-Boolean error where the Jar finds no error (main declined it by chance, in the
engine), and the `IF` and `CASE` shapes were wrong on main too; an indexed `Warshall` replacement
of a user's `TransitiveClosure` module gave a false success where main declined. The front end
now resolves the index's targets and declines where the model may evaluate one, and every
index whose classes, startup prints or calls it can't tell (see "Java overrides that stay
declined"). Out-of-suite probes (152 models) against the pinned Jar, main and the native checker
cover the assume, init, next, invariant, property, VIEW, ALIAS, CONSTRAINT and ENABLED contexts,
dead branches and short-circuits,
class-literal and `Class.forName` indexes, INSTANCE copies with and without substitutions, LET,
operator arguments, recursion, constant definitions, global and module-scoped configuration
values and substitutes, configuration names, wrong modules, identifiers and arities, standard modules' operators (`Any`, `:>`,
`+`, `Len`, `SelectSeq`, `Cardinality`, `Print`, `ToJson`), warnings, static initializers,
private, instance and final methods, `@Evaluation` and `@TLAPlusCallable`, and an index that
implements no interface or is named `tlc2.overrides.TLCOverrides.class`: the native checker
matches or declines each, with no wrong output, where main is wrong on 66 of them and the
checker before this change on 77. It declines three shapes main matched by chance, each because TLC computes the replaced method's
value where nothing printed shows it: a NEXT that assigns it and a VIEW that reads it (the
states differ but aren't printed), and a `final` method without parameters, which
`MethodValue.get` calls as TLC starts (a printing one makes main wrong). The `startup_checks`
fixture `member-display-indexed-user-value` matched only because its replacement of `TLC!:>`
prints the same text as the function `1 :> {1, "a"}`; with a replacement returning 7
(`index-builtin-printed`), main and the checker before this change print TLC's built-in result where
the Jar prints 7. It now declines, with TLC's output kept in `jar.out`. The `index-*`
fixtures of `startup_checks` record these shapes against the pinned Jar.

The front end first matched only a definition the named module itself wrote, where TLC's
`getOpDef` searches the module's whole context, and a builtin by the engine's spelling, not
SANY's. An annotation naming the root module, or a module that extends the real one, gave a
false success where main declined: `Warshall` with `module="M"` or a module that extends the
user's `TransitiveClosure` (Jar exit 151), `Any` with `module="M"` or `"Aux"` that extends `TLC`
(exit 75 and 10), and `Make` of a module extended through another under `\A i \in {1}` (an
error where the Jar finds none). The same gap gave false successes on main and the native checker for
a target an EXTENDS, an INSTANCE or a LOCAL INSTANCE brings in, `+`, `Len` and `Assert` through
`TLC`, `TLCExt` or a user module, and `\leq` and `\geq`; a printing or exiting method TLC calls
as it starts through an unused constant definition, a function or an instance copy; and an index
whose `get` returns null or holds one, that isn't public, or whose constructor is private (Jar
exit 255). The front end now resolves the target as `getOpDef` does, inspects the method's code
for a call as TLC starts, and reads the index's access. Of the 264 models (528 runs at one and
four workers) of that review and the 152 before it, none is answered wrongly; 8 runs where main
is wrong and 20 it declined now match. Four shapes main matched by chance now decline, besides
the three above, because TLC never calls a replacement main never knew of, or its value happens
to equal the body's: `+` replaced in a dead `IF` branch or a short-circuited ASSUME disjunct
(declined wherever the spec names it), `DOMAIN [x \in {1} |-> Make]` (the engine computes the
function's values, where TLC's `FcnLambdaValue` doesn't), and a PROPERTY whose replaced
`[](s = 0)` the method makes `TRUE`, which also holds. An unused definition over a quiet
replacement (`K == 1 + 1`, `K == 1 \in Any`), `<=` and `>=`, which SANY gives no operator, and an
index listing `String.class` now match, as on main.

All 102 recorded `trace-kept` models match the pinned Jar at one and four workers, with
`-noGenerateSpecTE`; main prints other than TLC on `assume-function-printing-in-place` and
`assume-function-printing-two-keys`. A finite function first demanded through a lazy argument
keeps its `FcnLambdaValue` class, conversion cache and copy behavior there.

TLC's action splitting reaches a variable inside an operator's application or an \E of NEXT, where
`getActionsAppl` catches the `ClassCastException` of the cast of the variable's declaration
(see "A variable or a constant as an action" for the cast it doesn't catch, which declines) and
takes the whole application or \E as one action named after the node TLC split, keeping the
actions it split from it before the variable. With `Init == x = 3`, `A == x` and
`Next == A \/ x' = x` (also `x' = x \/ A`, `B == A` with `Next == B \/ x' = x`,
`A == x \/ x' = x` with `Next == A`, `\E i \in {1} : x \/ x' = x` and two nested `\E`), TLC's
2247 failure lists every enclosing node in the 2103 stack (for `Next == A` over `A == x \/ x' = x`:
`0. Line 13, column 9 to line 13, column 9`, `1. Line 12, column 6 to line 12, column 16`,
`2. Line 12, column 6 to line 12, column 6`), where the binary prints the innermost frame only.
With `Init == x = TRUE`, the 2109 report and the trace name TLC's action by the application
(`<A line 14, col 9 ...>`, `<Next line 14, col 9 to line 14, col 24 ...>` for the \E), where the
binary gives the definition's body or the variable; a constant the configuration replaces by
`D == TRUE` (`c <- D`) TLC names `TRUE`, the binary `D`. An action TLC split before the variable
it keeps besides the whole (`B == x' = x \/ x`, `Next == x' = x \/ B`, `Init == x = FALSE`), so it
counts 4 states generated where the binary counts 3, with no error found by either. main prints
the same as the binary on all of these. `getActionsAppl` casts the operator of a name it doesn't
look up to a definition (a variable, a constant, a formal parameter, a bound name) to
`OpDefNode`, and the innermost operator's application whose definition it walks catches the
ClassCastException and takes that application whole as one action, after the actions it split
of it before: an application with arguments of constant level (`B(p) == c \/ x' = (x + p) % 3`
with `Next == B(1)`, whose 2109 report says "the next-state action" where the binary named the
action `B` and main `B(1)`; `C(r) == c` with `B(p) == C(p) \/ ..`, which TLC names `C` at the
application), a LET's definition (`LET q == c IN q \/ ..`, which TLC names `q` at the name, the
binary and main at its body), or a definition without parameters TLC didn't compute as it started
(`bb == x' = (x + 1) % 3 \/ c` with `Next == bb \/ x' = x`, which TLC splits into two actions and
counts 4 states generated where the binary counted 3). A formal parameter is cast so too (`B(p)
== x' = (x + 1) % 3 \/ p` with `Next == B(FALSE)`, 7 states generated in TLC, 4 in the binary),
and an \E catches it, taking the whole \E as one action in place of those it split (`\E v \in
{1}: x' = v \/ c`, whose report says "the next-state action"). main printed the same as the binary
on all of these. The binary now declines each such next-state relation ("a variable, a constant
or a parameter TLC's splitting of the next-state relation fails to cast to a definition inside an
operator's application, a LET's definition or an \E, which it then takes whole as one action",
`reaches_application_cast`), but where the name cast is FALSE, a constant the configuration sets
so or a parameter whose argument is the literal, before any action of the application (`B(p) ==
c \/ x' = (x + p) % 3`, `B(p, q) == q \/ ..` with `B(1, FALSE)`), where the whole adds no step to
the engine's, as on main. A definition without parameters TLC computes as it starts is looked
up to its value and taken whole, as the engine does (`bb == c`, `cc == bb`, `bb == LET q == c IN
q`, with `B(p) == bb \/ ..`, all matching, as on main).

An initial predicate with a bare variable as a disjunct (`Init == x \/ x = 3` or `x = 3 \/ x`):
TLC reports "2247 In computing initial states, TLC expected a boolean expression, but instead found
line 10, col 10 to line 10, col 10 of module ..." where the binary reports 2280 ("In evaluation,
the identifier x is either undefined or not an operator."), as for an INIT naming a definition
whose body is a bare variable (below). main prints the same as the binary.

With `S == {1}` and `Init == x = 1 /\ S /\ y = 1`, TLC has cached `S` at startup and reports coded message 2247 at its use. The native checker matches this; main walks into the definition and reports the expression at its definition.

A parameterized print such as `F(v) == PrintT(v)` with `ASSUME F([{1} -> {2, 3}] \ ({1} \cup {}))`
fails differently on main: TLC deep-normalizes the print's copied argument before it expands the
difference, while main's evaluator tests its right operand in written order, so TLC reports
comparing `<<2>>` with `1` and main reports testing equality of `1` with `<<2>>`. The native
checker declines it (`values TLC can't compare` in an assumption, `a startup definition that
fails` where the search computes it), as it does a direct print where it can't prove the tested
set safe.

A subscript of `[][Next]_v` in which something the front end can't follow, such as a subexpression
name, comes before an operator that leads back to itself, run with -nowarning: TLC's
SubscriptCollector reads on into the operator until its stack overflows and prints the
StackOverflowError (exit 255), where the front end stops at the part it can't follow, takes the
warning for unknown, which -nowarning lets pass, and checks the model. On main alike, which reads
no such operator at all. To fix it, read the rest of the subscript for a reading that doesn't end
before taking the warning for unknown.

An initial predicate or a next-state relation that applies a parameterized INSTANCE in a LET to a
variable, `Init == LET Q(v) == INSTANCE Inner WITH a <- v IN Q(x)!IInit`, with INIT and NEXT: the
front end reads the definitions the INSTANCE makes as of constant level, so it evaluates `x` as it
starts and fails ("In evaluation, the identifier x is either undefined or not an operator.",
exit 75), where TLC checks the model. On main alike. A SPECIFICATION that reaches one declines (`a
parameterized INSTANCE in a LET of the specification`); a property or an invariant reads it as
TLC does. To fix it, level the definitions a parameterized INSTANCE in a LET makes by their
arguments.

A property through a parameterized INSTANCE whose zero-argument initial operator is a bounded
quantifier over a nonempty substituted set can report that conjunct by its source range where TLC
names the operator. For example, `AInit == \A k \in S : v = 0` in `A(y) == INSTANCE Abs
WITH v <- y, S <- {1}` has this difference when the implied initial predicate fails. The
empty-set case remains a match.

A scoped configuration substitution of an external module's zero-argument `AInit` with a false
operator, used through a parameterized INSTANCE property, can leave the original implied initial
predicate in place: TLC reports the trivially false specification (exit 151), while the native
checker reports an initial property violation (exit 13). This is a body ToolObject replacement
case; the name-only INSTANCE correction does not model that replacement.

A parameter-free subexpression selection retains SANY's actual `$Nop` application through the
IR. Its value and action evaluation follows the selected expression, but GetVar and the
subscript collector keep the selector opaque. Thus `V!lab` and `V!1` in `[][Next]_v` warn about
the omitted variables as TLC does. A direct label remains transparent to GetVar; parameterized
selections retain their lambda application rather than acquiring an invented `$Nop`. Selected
operator arguments and definition symbols keep SANY's direct OpArg or OpAppl node. The selector
call and selected body's source ranges remain distinct.

An intersection or a difference TLC doesn't reduce, of sets of tuples, records or functions it
holds lazily with a part it can't size: TLC enumerates the left set and tests each element in the
right one (`SetCapValue.elements`, `SetDiffValue.elements`), which fails on a value of the wrong
kind, or comparing a function's domain with a set TLC overrides, where the engine intersects the
two sets it enumerated and tests nothing. `Init == x = PrintT(<<[{} -> STRING] \cap ([Nat -> {}] \
{})>>)` stops TLC with "Attempted to compare overridden value Nat with non-overridden value:\n{}" (exit
75), where the native checker prints `<<{}>>`, and `Init == x = [f |-> ((SUBSET Nat \X (1..0))
\cap (SUBSET Nat \X {})) \cap [STRING -> {}]]` stops TLC as a state it fails to fingerprint, where
the native checker finds no error. A reduced intersection or difference with such a set, as
`Cardinality({(Int \X {}) \cap {"a"}})`, tests the other operand's elements in it as TLC does.
On main alike, five of 1,600 adversarial specs; found by the
startup fuzz of PR 366.

A membership in DOMAIN of a function TLC keeps lazy over a value that isn't a set, as `1 \in
DOMAIN [e \in 1 + 1 |-> e]` (or over `N`, `Len(..)`, `1 < 2` or a model value `mv`), in the init,
next, invariant and property contexts, TLC reports as a value it fails to fingerprint ("TLC was
unable to fingerprint." with the Fingerprint Stack Trace, 2147), the domain having the source
DOMAIN gives it, where the native checker prints the failure with the nested expressions (2103).
This is unchanged on main.

TLC fails with "Attempted to construct a set with too many elements (>1000000)." where it converts
a set it keeps lazy of more than 1,000,000 elements (`toSetEnum` into a default `ValueVec`), as
`Cardinality(UNION {1..2000000, {}})`, and where it reduces the operation
(`Cardinality((1..2000000) \cup {})`, `(1..1000001) \ {}`, `(1..2000000) \cap Nat`,
`{0} \cup (1..1000001)`). The native checker fails as TLC does, or declines where it can't tell
how TLC holds the set (see "Sets past `TLCGlobals.setBound`"); main answers the first wrong.

The engine and the trace evaluator test a union, an equality of sets and a membership in a UNION
in an order other than the one in which TLC holds the sets' elements unnormalized, so a failure
there names other elements than TLC's (found by #327's adversarial round; each wrong on main
alike). Those that now match or decline are under "Earlier wrong outputs"; these remain:

| Repro | TLC | Native |
|---|---|---|
| `PrintT({1, "a"})` with `CONSTANT PrintT(1) = TRUE` | formatting the integer key's equality diagnostic normalizes the argument and fails with string comparison against `1`, outer 2105 only | integer equality against the unnormalized `{1, "a"}`; unchanged on main |
| `LET r == [b \|-> 1, a \|-> 2] IN 2 \in DOMAIN r` and `2 \in DOMAIN [[b \|-> 1, a \|-> 2] EXCEPT !.a = 3]`, where TLC holds the domain of a record it hasn't normalized unnormalized (`RecordValue.getDomain`) and the evaluator knows that only of a record constructor written in place as DOMAIN's operand, so it holds this one sorted | `Attempted to check equality of string "b" with non-string:\n2` | `Attempted to compare integer 2 with non-integer:\n"a"` |

A module instantiated by the name of a module nested in an EXTENDed module fails to parse where
SANY finds it: with `Holder.tla` holding `---- MODULE Held ----` nested, `EXTENDS Holder` then
`J == INSTANCE Held` stops with "Cannot find source file for module Held imported in module M."
(exit 150), where TLC checks the spec. `tests/unit/modules.test.ts` ("sees the nested modules of
an extended module") checks it with the TypeScript check until the front end matches.

A module file holding a UTF-8-encoded surrogate (`ED A0`–`ED BF` and a byte after) reads otherwise
than TLC reads it in the CLI of `dist/`. SANY reads a file through Java's
`InputStreamReader(stream, "UTF-8")` (`TLAplusParser`'s constructor), which replaces each such
three bytes with one U+FFFD, and the CLI's `readFileSync(path, "utf8")` with three. With
`"\xED\xA0\x80"` in a string, TLC prints `Len` of it as 1 and the CLI as 3. Every other sequence
that isn't UTF-8 decodes alike in both (compared over 8,150 sequences of one to four bytes). The
binary's `read_to_string` gives such a file no text and declines it.

A function over a domain TLC keeps lazy, applied at one point, fails where TLC computes only that
point: `ASSUME PrintT([s \in SUBSET {1} |-> 1 \div Cardinality(s)][{1}])` prints `1` in TLC.
`Tool`'s OPCODE_fc keeps a function constructor lazy under KeepLazy, which an application gives
its function's expression, and `FcnLambdaValue.apply` evaluates the body at the key with the
application's own control, so a constructor in that body is built at once unless that application
is itself the function of another. The engine marks, as it compiles an application, the
constructors that may be its function's value: the constructor itself, a branch of an IF or CASE
whose tests evaluate no definition, a definition without parameters or one applied to values, a
parameter's or a LET's argument, a function a LET defines, and the value at a key of such a
constructor applied to values (`[x \in S |-> [y \in T |-> e]][1][1]`). Only such a constructor,
as the application evaluates it, is built and, where that fails at some key with no print, draw or
register write, kept lazy instead (`lazy_function::build` over the sets it evaluated), evaluating
its body only where it is applied. So too, wherever it is evaluated, a constructor over a set TLC
doesn't reduce (`S \X T`, `SUBSET S`, a set of functions or of records), which TLC keeps lazy
whatever the control: `DOMAIN [p \in {1} \X {2} |-> 1 \div 0] = {<<1, 2>>}` holds in both. No
cache keeps that lazy value, as TLC, whose
`processConstantDefns` kept no value of a definition that failed, evaluates the definition anew
where it isn't applied: `G == [x \in {0,1} |-> 1 \div x]` with `G[1] = 1 /\ DOMAIN G = {0,1}` fails
at `DOMAIN G` in both. A constructor elsewhere in the function's expression (`{[x \in S |-> e]}`,
an IF's test, an argument that isn't a value) is built at once, and where TLC keeps it lazy and
the build fails, the replay declines. TLC's LazyValue keeps for a LET's later uses the function
its first use kept lazy (`LET f[x \in 1..2] == ... IN f[1] = 7 /\ DOMAIN f = 1..2` holds in TLC),
where the engine builds it again and fails; the replay declines (`a function a LET defines, which
TLC kept lazy where it first applied it`). What else meets the lazy function stops the engine as it
does for one over Nat: comparing, fingerprinting, printing it or a state holding it (which the
search checks for whatever it compiled). The replay, which builds the function, follows it where a
constructor of one name, written in place as the function an application applies, or the base of
EXCEPTs that function updates, whose body has no effects and no prime, UNCHANGED or
ENABLED (which TLC evaluates as an action where an action applies the function), fails in its body
as it builds it, with a failure TLC words: it holds the FcnLambdaValue TLC keeps, and applies it at a key,
updates it by EXCEPT (`select`, then `takeExcept`) and asks its domain as TLC does, a failure at
the key in the frames of the application or the EXCEPT, as `CallStackTool` hands on a copy of the
function without a source, whose failures are plain ones:
`[[x \in 1..2 |-> 1 \div 0] EXCEPT ![1] = 0][1] = 0` fails at key 1 in the EXCEPT's frame. A key
outside the domain of such a function, whose message's `toString` fails building it and prints it
unbuilt, which `CallStackTool` freezes its stack in, still declines outside an assumption ("the
body of a function TLC keeps lazy"); so does any other shape. That includes a constructor a LET
definition or an argument names (`LET f == [x \in 1..2 |-> IF x = 1 THEN 1 \div 0 ELSE x] IN
f[2] = 2 /\ DOMAIN f = 1..2`), whose `LazyValue` keeps the FcnLambdaValue from that first use:
TLC answers `DOMAIN f` from it without building it (`getDomain`), `toString` swallows the failure,
and a later use that builds it fails in the frames of that first use, none of which the replay
follows; and one a record, a tuple or a set holds.

A configured set replacement is read as the fresh enumeration TLC evaluates (see "Scoped
configuration entries"): with `CONSTANT Int <- Z`, `Z == {1}` and `ASSUME PrintT({1, "a"} \ Int)`,
TLC and the native checker report checking equality of integer `1` with string `"a"`, as they do
for `"a" \in Int`, `{1, "a"} \cap Int`, `Nat <- Z`, `Z == {"b"}` and the other receivers, in every
context. Applying a function whose domain is such a filter, `[x \in C |-> x]["a"]` with
`Z == {x \in {3, 1} : TRUE}`, declines (`values TLC can't compare`) where TLC converts the domain
and compares; main answered the assumption, whose output shows no source, and was wrong in the
other contexts, whose Fingerprint Stack Trace names Z's body.

A finite function whose domain TLC keeps lazy can print its body before a later operand fails.
`ASSUME PrintT([k \in SUBSET {1} |-> Print("body", k)] @@ (1 \div 0))` prints two body
values in the native checker, where TLC reports division by zero without either print. A
Cartesian-product domain has the same problem. `Tool` keeps these function constructors lazy;
`OpValue.eval` evaluates the second operand before `TLC.CombineFcn` converts either function.
These operand-phase failures already differ on main and are outside the new merge-error
admission, which leaves them unchanged.

A set of tuples, functions or records TLC fails to print, written inside another value, prints as
the engine enumerated it: TLC prints such a set by sizing its parts in order up to an empty one
and then asking each whether it is empty (`SetOfTuplesValue.toString` and `elements`, and their
siblings for functions and records), which fails on a part it can't size, such as Int, or on a
value that isn't a set. Where the set is Print's or PrintT's argument as written, the engine
builds it as TLC holds it and walks the same parts first (`Lazy::check_printed`), so `ASSUME
PrintT(Int \X {})` fails as TLC does. Nested in another value, as in an invariant `PrintT(<<Int \X
{}, x>>)`, it prints `<<{}, 0>>` where TLC fails (exit 75), on main alike. A constant definition
TLC computes at startup that may print such a set elsewhere than as an argument so written
declines ("a set TLC may fail to print, at startup", `may_hold_unsized`), and so does one whose
argument has a part the walk can't size as TLC does ("printing a set whose part TLC may fail to
size"), such as `[x \in Nat |-> x]`; a print anywhere else waits on the engine keeping how TLC
built the set, since declining it by its text alone would also decline prints that match, such as
`PrintT(SUBSET (Int \X {}))`.

A function from strings whose keys are Unicode letters and digits beyond ASCII prints as a function
where TLC prints a record: TLC tests each character of a key with Java's
`Character.isLetterOrDigit` (FcnRcdValue), so `PrintT("x٣" :> 5)` (U+0663, a decimal digit) prints
`[x٣ |-> 5]` in TLC and `("x٣" :> 5)` natively. `tests/unit/check.test.ts` ("prints empty intervals
and keys that are not field names like TLC") checks it with the TypeScript check.

A copy's definition without parameters that reads an INSTANCE substitute which prints, itself read
twice (`D == S`, `Op == D /\ D` in the inner module, `I == INSTANCE Inner WITH S <- PrintT(5)`,
`Test == I!Op`), prints `| 5` once where TLC prints it twice, as main does: TLC evaluates the
substitute again at each read of D.

A function over the power set of the empty set whose values are records, printed where an earlier
name or record has interned their fields in another order (`z == [b |-> 0]`, `PrintT([v \in
SUBSET {} |-> [a |-> 1, b |-> 2]])`), prints `({} :> [b |-> 2, a |-> 1])` where TLC, which keeps
the function lazy over `SUBSET {}` and builds its value at the print, prints `({} :> [a |-> 1, b
|-> 2])`, as main does: the engine builds `SUBSET {}` as the set `{{}}` it equals, and the
function over it as one TLC builds and normalizes. Over `SUBSET {0}` and other power sets, products,
function sets and record sets written in place, the binary prints the records as written, as TLC.

A record TLC compares with itself prints its fields in another order: TLC's equality normalizes the
record, so after `[fld2 |-> 0]` has interned fld2 first, `ToString(LET r == <<[fld1 |-> 1, fld2 |->
2]>> IN IF r = r THEN r ELSE r)` gives `"<<[fld2 |-> 2, fld1 |-> 1]>>"` in TLC and `"<<[fld1 |-> 1,
fld2 |-> 2]>>"` natively. `tests/unit/check.test.ts` ("sorts a record TLC compares with itself and
the records inside it") checks it with the TypeScript check.

A successor whose value fails as TLC fingerprints it is reported as an evaluation failure where TLC
reports a fingerprint failure. With `Filter == {n \in SUBSET {1} : 1 \div 0 = 1}`,
`Next == x' = Filter /\ {} = x'` (or `x' = 1 /\ {1} # Filter`), TLC prints the division, the
behavior, then "TLC was unable to fingerprint." with its Fingerprint Stack Trace and exits 75; the
engine prints the same frames as "The error occurred when TLC was evaluating the nested
expressions" and exits 255. A set TLC keeps lazy that fails to enumerate as TLC fingerprints the
successor does the same with the exit code right: `\E n \in ({1} \cup 2) : x' = n`,
`x' = x /\ \A n \in ({1} \cup 2) : TRUE`, `x' = CHOOSE n \in ({1} \cup 2) : TRUE` and
`x' = Cardinality({n + 1 : n \in ({1} \cup 2)})` print the nested expressions where TLC prints its
fingerprint failure, and `x' \in {1} \cup ({1} \cup 2)` leaves out the last frame of TLC's
Fingerprint Stack Trace. `tests/unit/check.test.ts` ("reports the sources of a set the replay of %s
fails to enumerate", "reports the left side of %s that fails to compare") checks them with the
TypeScript check.

Adding a state to the behavior graph that fails after an invariant violation leaves out where it
fails: with `Fair == x' = 1 \div (x - 1)`, `Next == x < 3 /\ x' = x + 1`, `Inv == x < 2`,
`Spec == Init /\ [][Next]_x /\ WF_x(Fair)` and `PROPERTY Live`, `INVARIANT Inv`, TLC prints after
the trace "The error occurred when TLC was evaluating the nested expressions at the following
positions:" with three frames, and the engine prints the rest alike without it; both exit 12.
`tests/unit/tlc-replay.test.ts` ("prints where adding a state to the behavior graph fails after a
violation") checks it with the TypeScript check.

`RTBound` of TLC's RealTime module, whose body holds `\EE`, applied in an initial predicate, was
declined by the engine (`unsupported: expression UnboundedQuantifier`) and reported by the
TypeScript check as "TLC cannot evaluate an unbounded quantifier at line 20, column 6", where TLC
reports "TLC encountered a temporal formula (\EE) when evaluating a predicate or action." with the
same frames and exit code. The engine now stops where it evaluates a quantifier without a bound,
and the trace evaluator words TLC's failure: `Tool`'s OPCODE_ue and OPCODE_uf ("TLC attempted to
evaluate an unbounded \E.") for `\E x :` and `\A x :`, and OPCODE_te and OPCODE_tf
(`TLC_ENCOUNTERED_FORMULA_IN_PREDICATE`, "\EE" or "\AA") for a temporal quantifier, which the IR
marks with the unbounded quantifier's second flag bit. Inside ENABLED, where TLC words an
unbounded quantifier in an action's position apart ("In computing ENABLED, TLC encountered
unbounded quantifier.") from one it evaluates, the evaluator declines (`an unbounded quantifier in
ENABLED`), as it does an unbounded CHOOSE there. `S \subseteq T` tests each element of S in T's
`member` within S's own method, and where S has a source, as `CallStackTool` gives the sets it
builds, `getNewHead` wraps a failure there in a FingerprintException ("TLC was unable to
fingerprint." with a fingerprint stack). A failure in a filter's predicate froze the call stack
within the predicate first (`CallStack.freeze`), as `CallStackTool` evaluates it, so the
FingerprintException takes none of S's source: TLC prints the frozen frames under "Fingerprint
Stack Trace", as the evaluator now does, for `{1, 2} \subseteq {x \in Nat : x \div 0 = 1}` and
for a filter inside a `\cap`, `\cup`, `\` or UNION with a source. `SetPredValue.member` words an
EvalException of the set's membership or of the predicate as "Cannot decide if element", a
predicate that isn't a boolean as "The evaluation of predicate ... yielded non-Boolean value."
(naming the predicate as SANY's `toString` does, a numeral by its image, as `5`, `\b101` or `007`;
a numeral the evaluator can't word declines, `a lazy filter's predicate that isn't a boolean,
written as a numeral`), and an element that isn't a tuple of a tuple pattern's names as "... is an element of a set of
N-tuples.", each a TLCRuntimeException, as no `SetPredValue` has a source
(`CallStackTool.evalAppl` returns a copy of it, which also evaluates the predicate with the
`CallStackTool`). A filter TLC built with the `Tool` that keeps no call stack, as a constant
definition computed as TLC started, and holds inside another value, which no `evalAppl` copies
(`T == {{x \in Nat : x \div 0 = 1}}` with `1 \in UNION T`), evaluates its predicate without
frames, which the replay doesn't follow: a failure there still declines outside an assumption
(`the membership of a filter TLC keeps lazy`), and so does an element of a tuple pattern TLC
keeps lazy, whose `toTuple` builds it. A set whose method a predicate's failure passes through
that is an interval a node TLC gives a source returned, as DOMAIN does (`OPCODE_domain`'s
`setSource(expr, getDomain())`, `DOMAIN <<1, 2>> \subseteq {x \in Nat : x \div 0 = 1}`), has a source
in TLC that the replay, holding an interval without an address, doesn't give it: such a failure
declines too (`the membership of a filter TLC keeps lazy`).
TLCGet("-D"), a system property without a name, declines in the engine
(`TLCGet of a system property without a name`): `System.getProperty` throws "key can't be empty",
where the engine had read the key itself, as `main` still does.

A file that instantiates or extends its own inner module of the file's name, as `---- MODULE B ----`
holding `---- MODULE B ----` and `I == INSTANCE B` does, declines (`a module that names a module of
its own name`), where TLC checks it: SANY scopes the inner module's context, which the front end
keys by name. It panicked before. It comes back once the front end scopes contexts as SANY does.

The adversarial rounds of the extended file's inner modules and of the library's typed errors
found these, each wrong on main alike:

| Repro | TLC | Native |
|---|---|---|
| A root inner module named `Sequences`, `Naturals`, `TLCExt` or `_TLCTrace`, in TLC's default mode, which writes the trace exploration spec | `Multiply-defined module '<X>'` | checks the model |
| `EXTENDS A, B` where A and B each hold an inner `---- MODULE In ----` | SANY's warning "the declaration of 'In' conflicts with its declaration at …" | no warning |
| `K == INSTANCE B`, B `EXTENDS A` and holds an inner `In`, as A does | `*** Errors: 1`, the multiply-defined module | `*** Errors: 2`, adding "Substitution error, probably due to error in module being instantiated." |
| `EXTENDS B, A` where B instantiates `In.tla` and A holds an inner `In` | `Multiply-defined module 'In'` at A's | checks the model |
| A constant definition `P == PrintT("in")` in a module the spec instantiates | prints `"in"` for the module's definition and again for the instance's | prints it once |
| `P == PrintT("hi")` with a configuration error, such as `NEXT Nope` | prints `"hi"`, then the error | the error alone |
| `CONSTANT K <- D` with `CONSTRAINT D`, D a set | `TLC expected a boolean value, but did not find one.` at D's definition | `The constraint of D is equal to {1}` |
| A circular dependency SANY finds as it loads the files, with standard modules to load before the cycle closes | stops at the cycle | parses those modules first, as it finds the cycle once it has loaded every file |
| A constant definition that applies AssertEq, which TLC computes as it starts, with a configuration error, such as `NEXT Nope` | `D == AssertEq(1, 2)`: prints `"Assertion failed"`, `1` and `2`, then the error | the error alone |
| A decimal an INSTANCE substitutes | `I == INSTANCE Inner WITH c <- 1.5`, unread | checks the model | `TLC can't handle real numbers.` |

The PrintT ones wait on steps 2 and 3 of [startup.md](startup.md). The library's check and the
native front end decline them ("what the spec prints as TLC computes its constants"), the latter
for an undefined name the configuration's invariants, INIT, NEXT or properties give too
(`D == PrintT("d")` with `PROPERTY Undef`), where a constant definition that reaches a print
doesn't evaluate in the constant evaluator, which computes no print: `D == IF FALSE THEN
PrintT("d") ELSE 1` prints nothing and the error is answered as on main: where the front end stops at an error
TLC reports after it computes the constant definitions, and one of those may print
(`may_print_constant_definitions`), and where the engine stops as it starts having left out a
constant definition that applies a TLCExt builtin. The AssertEq one declines there alike.
`CONSTANT K = 3000000000`, `CONSTANT K <- Nope` with K undeclared and a constant unassigned, and
`D == AssertEq(1, 2)` without a configuration error match TLC, where main printed other than TLC.

A register probe that prints declines alike before a configuration error. TLCSet has no minimum
level in Java (`TLCGetSet.TLCSet`), so `getLevelBound` counts a definition with no parameters that
reaches it constant, and `processConstantDefns` computes it, printing until TLCSet fails on no
checker, which it swallows; the definition facts count TLCSet of state level, so the front end
counts such a definition among those that may print by `getLevelBound` itself
(`StartupPrints`): `D == PrintT(8) /\ TLCSet(1, 2)` (or `Print(8, TRUE) /\ TLCSet(1, 2)`,
`PrintT(8) /\ TLCSet("exit", FALSE)`, `PrintT(8) /\ (FALSE => TLCSet(1, 2))`, `LET s ==
TLCSet(1, 2) IN PrintT(8) /\ s`, `IF PrintT(8) THEN TLCSet(1, 2) ELSE TRUE`, `{PrintT(8)} \cup
{TLCSet(1, 2)}`, `TLCSet(1, PrintT(8))`, `LET r == RandomElement(1..10) IN PrintT(r) /\ (r > 100
=> TLCSet(1, 2))`), read or unread, with no INIT, or with an INVARIANT, PROPERTY, CONSTRAINT,
ACTION_CONSTRAINT, VIEW or SYMMETRY the spec doesn't define, where TLC prints `8` before 2231
or 2229 and main prints the error alone. One that reads a variable (`PrintT(v) /\ TLCSet(1,
2)`), or TLCGet, which has `minLevel = 1`, TLC doesn't compute there, and it answers.

The front end binds a name to an inner module of an extended file as SANY does
(`resolveNamesBetweenSpecAndExtention`) only where its first load stops at "Cannot find source
file" for the name, every module of the spec has a name of its own, at any depth, and the name
names no file or standard module. There binding by name is SANY's binding by scope. Elsewhere it
reports what it reported before, which differs from TLC where SANY binds the name:

- where the name also names a file or a standard module, it reads that file, where SANY reads none
  and uses the inner module;
- where two modules of the spec share a name, two inner modules or an inner module and a file or
  standard module, it reports "Cannot find source file";
- where a file extends a name bound to an inner module that extends another file, it reports
  "Cannot find source file" too.

Each comes back once the front end scopes an inner module's context as SANY does, instead of by
name; branch `extended-inner-lexical` holds a version that tracks more of SANY's scopes by name.

These print a "states generated" other than TLC's today, outside the corpus and the tests; why,
with TLC's source, is in [lazy-duplicates.md](lazy-duplicates.md):

| Shape | Repro | TLC | Native |
|---|---|---:|---:|
| A held SUBSET or set of functions `\cup` a set that overlaps it | `Init == s = 0 /\ x = 0`, `Next == s' = SUBSET {1} /\ x' \in s' \cup {{1}}` | 10 | 7 |

An adversarial pass on #292 (2,267 specs against TLC at d8fb231, main 40009ac8 and the branch)
found these on main, which the branch prints alike:

| Shape | Repro | TLC | Native |
|---|---|---|---|
| A failing conjunct of the specification that is an operator applied to arguments, or an inline LET or LAMBDA | `P(n) == n = 1 /\ Assert(FALSE, "x")`, `Spec == P(1) /\ Init /\ [][Next]_x` | the frames of the body TLC inlines | adds the application's frames first |
| A POSTCONDITION that sets a register | `Post == PrintT(IF TLCSet("exit", FALSE) THEN 1 ELSE 0)` | prints `1` once, then `The post condition Post cannot be a constant.` | prints `1` twice and passes |
| An ALIAS the configuration substitutes a constant definition for | `D == TRUE` (or a record, a set, a tuple, `-1`, a LET), `CONSTANT C <- D`, `ALIAS C` | the alias's value | `_ALIASEvalError = "The alias C cannot be a constant."` (the TRUE case is fixed on the ALIAS branch, alias-trace-fixes) |
| An ALIAS or a POSTCONDITION that is a literal, or that the configuration substitutes one for | `Alias == 3`, `ALIAS Alias`; `Post == "a"`, `POSTCONDITION Post` | `The alias Alias cannot be a constant.` or TLC's message for the postcondition | runs it as a definition (the constant-alias branch's `Definition::LITERAL` fixes it) |
| A PROPERTY the configuration substitutes an empty `\A` for | `C <- D`, `D == \A i \in {} : FALSE`, `PROPERTY C` | `Temporal formula is a tautology` | passes |
| A violated invariant of an instance inside a PROPERTY | `PROPERTY Prop`, `Prop == [](I!IInv)` | `Invariant I!IInv is violated.` | `Invariant IInv is violated.` |
| An INVARIANT the configuration substitutes a temporal formula for | `INVARIANT C`, `C <- D`, `D == [](x > 0)` | names D, or fails at run time where another invariant reads C | names C, or fails as it starts |
| A tuple or a lexing error in a configuration's value | `CONSTANT K = <<"a">>`, an unclosed string | a lexical error | a parse error, or another position |
| A subset test whose lazy union fails only after an earlier element already disproves it | `ASSUME PrintT(({-1,7} \cup (Nat \cap SUBSET {1})) \subseteq {})` | prints FALSE and succeeds without reaching the later failure | may force the union and fail |
| A lazy difference streaming a held nonempty power-set filter against a scalar enumeration | `LET F == {v \in SUBSET {1} : TRUE} IN PrintT(F \ {1})` | reports a comparison with the set `{}` as receiver | reports testing equality of integer `1` with `{}` |
| A `\*` comment in a configuration with lone carriage returns | a cfg whose lines end in CR alone | ends the comment at the CR | comments out the rest of the file |
| A missing INIT or NEXT after a printing constant definition | `D == PrintT("d")`, `INVARIANT I`, no INIT | prints `"d"`, then the warnings and 2231 | declines (`what the spec prints as TLC computes its constants`); without a print, it prints `processConfig`'s warnings (2149, 2139, 2140, 2255) before 2231 or 2232 as TLC does |
| An INVARIANT the configuration substitutes an action for | `C <- D`, `D == x' = x` | names D in the invariant error | names C |
| A substitute for a definition before it in the module order, unread, defined in an EXTENDed module | `C` in an EXTENDed module, `D == PrintT("d")`, `C <- D` | prints `"d"` twice | once |
| A LOCAL INSTANCE of a module with a printing constant definition | `LOCAL I == INSTANCE N`, `N` has `P == PrintT("p")` | prints twice | once |
| A PROPERTY the configuration substitutes a TLCGet("level") predicate for | `C <- D`, `D == TLCGet("level") > 0`, `PROPERTY C` | no warning | warns of a state-level formula |
| A PROPERTY that reads TLCGet("level") | `Prop == \A y \in {1} : TLCGet("level") > 0`, `PROPERTY Prop` | no warning: SANY's level of the definition is constant, TLC's `getLevelBound` alone counts TLCGet's minimum level | warns of a state-level formula (2255), as main does |
| A predicate the configuration substitutes a TLCEval of TLCGet or of a state's Print for | `C <- D`, `D == TLCEval(Print(x, TRUE))` as an INVARIANT, a CONSTRAINT or a conjunct | TLC's message | another |
| A constant INVARIANT that writes TLCSet where TLC doesn't evaluate it | `Inv == IF FALSE THEN TLCSet(1, 2) ELSE TRUE`, or after `TRUE \/`, in an unused LET or argument | warns that Inv is a TRUE constant | doesn't |
| An INVARIANT the configuration assigns a value where the module defines it | `Inv == FALSE`, `CONSTANT Inv = TRUE` | warns and finds no error | warns, then reports `Invariant Inv is violated` |

The engine now declines the shapes that printed other counts here too: a constant definition
normalized elsewhere, then streamed (`C == UNION {1..2, 2..3}`, `Init == s = C /\ x = 0`,
`Next == s' = s /\ x' \in C`: TLC 13, native 17), a stream whose order alone differs from the
normalized set's (`(SUBSET {2}) \cup {{1}}` through a variable, a constant via a variable, a `\E`
name or a LET named twice), and a variable bound by `\in` to a set enumeration's lazy first
element (`Next == s' \in {UNION {1..2, 2..3}} /\ y' \in s'`: TLC 17, native 13).

Outside the counts, SANY's report differs on an INSTANCE of a module with semantic errors: for
`I == INSTANCE Other` with `Other.tla` holding `Op(n) == n - 1` and no EXTENDS, TLC prints
`*** Errors: 2` for module Spec, while the binary prints `*** Errors: 3`, adding `Substitution error,
probably due to error in module being instantiated.` at the INSTANCE (exit 150 in both).

TLC rejects a VIEW or a POSTCONDITION the configuration names by a definition it computed as it
started, as it does an ALIAS, but holds a definition whose body is a number or a string as written
and computes nothing for it (`SymbolNodeValueLookupProvider.lookup`, `Spec.getViewSpec`,
`getPostConditionSpecs`). The binary differs on one shape: a POSTCONDITION that is a number or a
string, `PC == "s"`, which it rejects as a constant (exit 255) where TLC evaluates it and reports
it not a boolean (exit 10). A VIEW TLC computes as it starts, `V == TRUE`, `V == {1}`, `V == A`
with `A == 5`, or a constant the configuration assigns, `CONSTANT C = 1` with `VIEW C`, is now
rejected as TLC rejects it ("The view function V cannot be a constant.", exit 151), before the
SYMMETRY, as `TLCStateMut.setTool` reads them. A constant VIEW the front end's evaluator can't
compute, which TLC computes and rejects after its effects (`V == PrintT("v")`, `V ==
RandomElement({1, 2})`, `V == ToString(3)`), declines with the evaluator's reason, as nothing
at startup checks a VIEW.

With one worker, a `-config` ending in `.tla` reads the named CONFIG section as TLC does,
including a section before the module, the first matching section, and configuration errors before
SANY; the `embedded-*` startup fixtures record these and neighboring extension handling against
TLC. With more than one worker, a configuration in a CONFIG section declines: three imported
liveness models expose parallel search counts and traces that differ from TLC, whose own results
also vary with worker scheduling. External `.cfg` files keep their existing behavior.

The binary declines a module file it finds but can't read, such as a directory or text not in
UTF-8 (`a module's file the front end can't read`), where SANY prints `***Internal error: Unable to
create NamedInputStream in toIStream method`. Where the TypeScript check finds the files, TLC's
`SimpleFilenameToStream` still differs from it on:

- `-config _CBORTrace.tla`, which TLC finds among its jar's standard modules and the CLI reports
  missing (the other standard modules decline);
- `-config` naming a resource at the root of TLC's class path, such as `pcal/PlusCal.tla`, after
  which TLC prints a `FileNotFoundException`'s stack trace;
- a `.class` file that isn't one (empty, truncated, `/dev/null` or a socket), which TLC rejects
  with `Found a Java class for module M, but unable to read it`, and a user's `Naturals.class` or
  `TLC.class`, which TLC tries to load;
- under `PROVE_IT_ENGINE=0` alone: options TLC doesn't know, which it rejects.

On Windows, the binary and the CLI find a spec's files by the host's rules (`host_path.rs`), and
print the forms of a path whose rendering TLC's source settles: SANY's `Parsing file` of a module
found by its real path is `Path.toRealPath`, which Java takes from `GetFinalPathNameByHandle` as
std's `canonicalize` does, without the verbatim `\\?\` prefix (`WindowsLinkSupport.getFinalPath`),
with `\` between the parts. The other forms decline (see "Declines to win back" below). Before
PR 364 the binary printed the verbatim prefix and a `(file:…)` URL with `\` escaped as `%5C` for
every module, as it compared the path it was given with the verbatim real path, and printed the
trace exploration spec's path with `/`.

Proofs: of the 33,025 obligations tlapm's record (`proofs.json`) proves, prove misses 6 on the
record of `prover-inputs.json`, where SMT, Zenon and Isabelle all fail. tlapm proved each with SMT
(prover.md, "Deviations from Z3", has the gate):

| Obligation | `smt` input | Why |
|---|---|---|
| SequencesExtTheorems_proofs #409 | b7775ca0b1b01064 | Z3 4.8.9 proves it, 5.3.3 times out; the port's search is longer |
| Bakery #89 | e67cda013bcdbc0e | the same |
| CRDT_proof #129 | 5390a15510ed57e1 | both Z3s prove it; the port needs 2,570,874 steps, above its limit of 1,321,216 |
| LamportMutex_proofs #574 | cf2bc77dbe72f5d0 | Z3 4.8.9 proves it, 5.3.3 times out |
| PaxosCommit_proof #345 | c4f10dabeaca0a49 | Z3 4.8.9 proves it, 5.3.3 times out; the port needs 10,358,109 steps, above its limit of 7,321,600 |
| Boulanger #240 | b2ca9ee96f3db516 | flattening clauses as Z3 4.8.9 does lengthens the port's search from 1,807,047 steps to 8,170,365, though its 4 distributions are 4.8.9's: open |

The specification reader now reports TLC's error for a configured FALSE operator with arguments
and for an action substituted into a specification conjunct. The corresponding INVARIANT
substitution, and the application, LET and LAMBDA failure-frame cases in the table, remain wrong.
The pinned-Jar `spec_shape` fixtures also cover temporal quantifiers rejected in a specification;
other quantifier shapes can still decline. The exact `TLCEval(PrintT(FALSE))` conjunct
listed in the earlier review prints `FALSE` once and succeeds in both TLC and the native checker;
this does not establish the order for every effectful conjunct.

These print other than TLC as main does, outside the corpus and the tests; a review of the ALIAS
cells TLC holds as values found them. Each spec has `VARIABLE x`, `Init == x = 0`,
`Next == x' = x + 1`, `Inv == x < 2` and `Q == [y |-> x]`:

| Shape | Configuration | TLC | Native |
|---|---|---|---|
| An ALIAS substituted by a definition the configuration assigns | `CONSTANT Alias <- Q`, `CONSTANT Q = 3` | "The alias Alias cannot be a constant." at each state | the trace through Q |
| An ALIAS assigned a value the front end can't normalize, on a run that prints a trace | `CONSTANT Alias = {1, "a"}` | "The alias Alias cannot be a constant." at each state | the trace through the spec's definition |
| A POSTCONDITION the configuration assigns | `CONSTANT PC = TRUE`, `POSTCONDITION PC` | "The post condition PC cannot be a constant." | another report |
| A POSTCONDITION naming a constant definition that holds a set TLC can't normalize, on a clean run | `Lit == {1, "a"}` (or `[a \|-> {1, "a"}]`, `SUBSET {1, "a"}`, `{{1, "a"}}`, `<<{1, "a"}>>`, `{TRUE, 1}`, `{<<1>>, 1}`, a LET of one), `POSTCONDITION Lit` | 2405 `Evaluating postcondition Lit ... failed.` and `TLC expected a boolean value, but did not find one.`, exit 10: `processConstantDefns` fails to normalize the value and keeps the definition, which TLC then evaluates as a postcondition | an unexpected exception and `The post condition Lit cannot be a constant.`, exit 255 |
| The same POSTCONDITION after an invariant's violation or a deadlock | `Lit == [a \|-> {1, "a"}]`, `POSTCONDITION Lit`, `INVARIANT Inv` | the trace, then the 2405 and 2215 lines | the trace without them |
| An ALIAS naming such a constant definition | `Lit == {1, "a"}` or `[a \|-> {1, "a"}]` (or `SUBSET {1, "a"}`, `<<{1, "a"}>>`, `{{1, "a"}}`), `ALIAS Lit`, on a run that prints a trace | the plain trace for `{1, "a"}`; for the record, the unexpected exception `Attempted to compare string "a" with non-string: 1` in place of the trace | every state with `_ALIASEvalError` and `The alias Lit cannot be a constant.` |
| An INIT naming a definition whose body is a bare variable | `Lit == x` (or `LET y == x IN y`), `INIT Lit` | 2247 `In computing initial states, TLC expected a boolean expression, but instead found` the variable's location | 2280 `In evaluation, the identifier x is either undefined or not an operator.` |
| An ALIAS substituted for a definition of a module both extended and instantiated with parameters, which TLC doesn't compute | `Y <- Alias`, with `Alias == 3` | the plain states | "The alias Alias cannot be a constant." |
| An ALIAS from an INSTANCE with substitutions that the configuration assigns in that module | `INSTANCE N WITH c <- 1`, N's `Alias == [y \|-> c]`, `CONSTANT Alias = [N] 3` | `y = 1` | the plain states |

At the level of inputs, #321 also moved ten `smt` inputs tlapm proves from `unsat` to `unknown`
that main proved: 0dfd248d2bdad02b, 12a106a46ac87d79, 181f3f94d6c23221, 2f279b8fcc0984d6,
52c873767bacfb3b, 6181e3d8679eef23, 6f1bb244e72ae33d, 8e48a4022642d1fc, b2ca9ee96f3db516 and
e8e512b5c0878a4e, and gained one. Z3 4.8.9 proves nine of the ten (all but 6181e3d8679eef23). Only
b2ca9ee96f3db516 (Boulanger #240) loses its obligation; Zenon or Isabelle prove the other nine's.

The engine's `decide` declines a text that holds a lone surrogate, so the obligation fails. A string
that is one would read as U+FFFD, two different strings would be one name, and the axiom that they
differ would prove anything. No obligation of tlapm's record holds one.

The SMT solver decides only the SMT-LIB tlapm's encoder writes (`script_subset.rs`). Two known
issues remain within that subset. tlapm's encoder writes neither shape, and no input of the record
reaches either:

| Repro | Z3 4.8.9 | The port |
|---|---|---|
| `(assert (= (* b1 b2 … b12) 1))`, a product of 12 binomials over 24 Int constants | sat at once | runs on: `nlsat::levelwise::add_linear_approximations` reaches `AlgebraicManager::select` and `Rational::floor`, which read neither the deadline nor the step limit |
| `(assert (distinct c0 … c11999))` over `Idv` | not measured | aborts the process: the rewriter's `mk_not` allocates past the size cap, which preprocessing never reads, and an allocation failure isn't caught |

EXCEPT selection follows `Tool.OPCODE_exc`: the base is evaluated first, then every component of
one update's path, then the complete path is selected before its right-hand side is evaluated.
A missing component keeps the original value and skips the right-hand side. Incompatible key
classes and failed equality checks remain evaluation errors. Missing paths report warning 2144
through the same ordered output journal as Print, including unused startup definitions, and
`-nowarning` suppresses it. The printer retains TLC's process-wide rendered-message deduplication.
The `except-warning-*` startup fixtures record the key, update, warning, and Print order against
TLC at d8fb231, including repeated updates, tuples, functions, startup, `-continue`, and an empty
configuration. The missing-key decline and missing startup warning described in the historical
measurements below are superseded by this behavior. Expression and recursive caches retain only
quiet evaluations; a successful startup definition still keeps its value after its warnings.
Captured startup results supply trace metadata without evaluating failed definitions again.
In the trace evaluator, an EXCEPT at a key that isn't an integer of a function over an interval
that it doesn't know TLC built declines ("EXCEPT at a non-integer key of a function over an
interval TLC may build"): built, TLC fails in `FcnRcdValue.select` ("Attempted to apply function
with integer domain to the non-integer argument"), and kept lazy it fails in
`IntervalValue.member` or, for an empty interval, warns. A constructor over an `IntervalValue`
that the evaluator knows TLC built (no KeepLazy, as `Tool`'s OPCODE_fc builds a Reducible
domain), or an EXCEPT of one, now fails as `FcnRcdValue.select` does; one written in place that
TLC keeps lazy fails as `IntervalValue.member` does where the interval isn't empty. Only an
empty interval kept lazy, or one whose class the evaluator doesn't know, still declines. Without it,
`CHOOSE x \in {1} : [[b \in 2..1 |-> b] EXCEPT ![<<-1>>] = x]` as TLC starts printed the warning
and TLC's non-boolean CHOOSE failure.

A missing-field warning encountered while eagerly constructing the function value of `f[e]`
still declines when TLC would keep that finite function lazy. The guard runs only when the
missing path is selected in that eager body. DOMAIN and other materializations retain their
warning order, and warning-free evaluations retain their ordinary caches. Java overrides whose
value construction is not understood retain their existing override decline.

A warning raised as the liveness checker evaluates an atom of the temporal properties (a state
or action predicate, ENABLED, or a fairness action's step: `Tool.OPCODE_exc`'s 2144 or the
2143 of an UNCHANGED that doesn't hold, `Tool.enabledUnchangedImpl`, under `LiveCheck`) fails
the atom instead ("a warning as the liveness checker evaluates an atom of the
temporal properties"), as main's engine did, so the run declines as one whose atom may fail to
evaluate: TLC prints 2144 between what its checker reports, unless its warning history already
holds the message, which the engine's tables, which drop the warning, don't place. Before, the
warning was lost, which printed `No error has been found` without TLC's 2144 for
`P == <>([<<x>> EXCEPT ![2] = 1][1] = 1)`, and omitted it before `Deadlock reached` for a warning
in `WF_x(...)`'s action; likewise TLC's 2143 for `A == x' = 1 - x /\ UNCHANGED x` in `WF_x(A)`
or `[]<>(ENABLED A) \/ <>(x = 1)`, where main is wrong too. TLC's search may not warn where its
ENABLED does (`processUnchangedImplVar` meets the conjuncts otherwise than
`enabledUnchangedImpl`), so an ENABLED whose walk may warn of an UNCHANGED variable is run, and
fails as it warns, rather than read off the search's steps, which dropped the 2143 of
`Next == A \/ B` with `WF_x(A)` (`unchanged-warning-*` fixtures). Otherwise an atom the
search's steps answer (Next itself, its pieces or TLC's actions) evaluates nothing, so a warning
Next raises still prints as the search raises it (`except-warning-*-liveness*` and
`except-warning-fairness-action` fixtures). To win them back:
place the warnings the atoms raise in the held output, deduplicated as MP's history is.

A failure in an argument of `f[a, b]`, as `[x \in {1}, y \in {2} |-> x + y][1 \div 0, 2]`, met in
a state or a step: TLC evaluates the arguments as the tuple SANY makes of them, a frame of its own
at the application's place, so its nested expressions list that place twice, where the replay
lists it once. Measured on the base source too (probes of 2026-11-18); not yet fixed, since that
tuple also has a source TLC's FingerprintException traces would name.

Outside the corpus, this shape prints other than TLC, and main is wrong on it too, with other
text (probes of 2026-11-18):

- A failure in a selection through a copy of a copy an INSTANCE with substitutions makes (`I ==
  INSTANCE Sq WITH K <- 0`, `Sq` having `J == INSTANCE Sm WITH N <- K`, and `I!J!V(1)!L`, or
  `J!V(1)!L` through an unnamed `INSTANCE Sq`), or in a substitute that is a name a selection
  through such a copy reads (`I(1 \div 0)!V(1)!L`, `N <- q`), in the initial predicate, the
  next-state relation, an invariant or a property: TLC prints the frame of each `SubstInNode`,
  and of the declaration's name before the substitute's, which the IR doesn't keep for a
  substitute that is a name, so the call stack lacks them (3 shapes probed, 12 runs). A
  substitute other than a name (`I == INSTANCE Sm WITH N <- 1 \div 0` and `I!V(1)!L`) now prints
  as TLC does. main prints the same stacks, and
  also lacks the frame of a selection through a single copy, which answers now (see "Call stacks
  of a selection"). The assumption context matches.

#### Sets past `TLCGlobals.setBound`

TLC builds a set enumeration element by element in a `ValueVec`, which fails once it holds
1,000,000 elements and is given another (`ValueVec.ensureCapacity`: `Attempted to construct a set
with too many elements (>1000000).`, a WrongInvocationException). It builds one so:

- where it enumerates a bound of `\E`, `\A`, CHOOSE or a set map, in an action too, in normalized
  order (`Tool.contexts`, OPCODE_bc: `EnumerableValue.elements(Ordering.NORMALIZED)`, then
  `toSetEnum`) and the set is one it keeps lazy: a product, a set of records or functions, or a
  `\cup`, `\cap`, `\`, UNION or filter it doesn't reduce, counting each element they stream,
  duplicates and all. An interval builds its array at once (`IntervalValue.toSetEnum`), a power
  set enumerates itself in that order (`SubsetValue.elements(Ordering)`), and a function's
  constructor walks its domain as built (`FcnLambdaValue`), so none of them fails there;
- where it reduces `\cup`, `\cap` or `\` with a set enumeration or an interval at once
  (`IntervalValue.cup`, `SetEnumValue.cap`, ...), unless the receiver of `\cup` is empty, and
  UNION of set enumerations (`UnionValue.union`);
- where it compares or sizes a set it keeps lazy as its normalized set (`convertAndCache`): `=`
  with a value of another class (two products, or two sets of records or functions, compare by
  their parts), `compareTo`, and the size of a lazy `\cup`, `\cap`, `\`, UNION or filter.

The engine fails at each (`Compiled::check_enumerated`, `Compiler::bounded_operation`, the UNION
builtin, `Lazy::size`) and the trace evaluator words the failure (`sets::check_enumerated_bound`,
`push_set_element`). It declines, past 1,000,000 elements:

- `a bound of more than TLCGlobals.setBound elements TLC may hold lazy`: a bound whose value TLC
  may keep lazy or hold built, such as a bound name's, a primed variable's or a function's value;
  an unprimed variable's is one TLC fingerprinted, which built it, and a set of sets is taken for
  a power set, which enumerates itself (so a UNION, `\cup` or filter of sets of sets TLC keeps
  lazy, held so, is a known wrong output);
- `a set operation of more than TLCGlobals.setBound elements TLC may reduce` and the same of
  UNION, where the compiled operands don't tell whether TLC reduces it;
- `sizing a set TLC builds past TLCGlobals.setBound elements` (Cardinality wraps the failure as
  that of its Java method);
- `comparing a set TLC builds past TLCGlobals.setBound elements`, which TLC words as a failure to
  fingerprint outside an assumption;
- `a set TLC keeps lazy past TLCGlobals.setBound elements, held in a value`: as an element of a
  tuple, a record or a set enumeration, which TLC compares, fingerprints and prints as its
  normalized set;
- in the trace evaluator, `a bound TLC tests the elements of past TLCGlobals.setBound`: a `\cap`
  or `\` that enumerates a set that may stream an element twice, or whose test fails; and `a UNION
  of set enumerations past TLCGlobals.setBound elements` in all, which it can't combine in time;
  and `a DOMAIN of more than TLCGlobals.setBound elements TLC may hold lazy`, the domain of a
  function TLC may keep lazy (`FcnLambdaValue.getDomain` is the set its constructor bound).

Known wrong outputs here, each of a set past 1,000,000 elements: a set enumeration TLC holds
unnormalized with duplicates, as a set map's, as the receiver of `\cup` (`SetEnumValue.cup` adds
its elements as held, the engine counts the normalized set); a set TLC keeps lazy that reaches a
comparison, a fingerprint or a print through a value the engine holds built other than a tuple,
a record or a set enumeration (the range of a function's constructor, an EXCEPT, a set map's
image, a primed variable's value) or through an operand with effects; and a bound `\cup` that
streams duplicates of a set the engine has no reference to. Probes of 2026-11-19 against the
jar: a product, a set of records and of functions, a lazy and a reduced `\cup`, `\cap` and `\`,
UNION, CHOOSE, `\A`, a set map, a tuple pattern, several bounds with an empty one, nested and in
each context, at 1 and 4 workers, all match or decline, and main is wrong on each that fails.

#### Runs TLC's own output makes unreproducible

Some corpus runs have no output a checker could reproduce, because what the pinned jar prints
depends on the JVM, not the spec. Each is listed, with its evidence, in `unreachable.json` beside
this file, and each must decline. Each was run through the corpus's harness on the pinned jar 5
or more times with different heaps (`-Xmx`), stack sizes (`-Xss`), compilers or wall-clock
stalls (the JVM frozen with SIGSTOP), and each is checked against TLC's Java and tla-ts's checker.

- Heap (6 runs, `random_00102`, `01576`, `03717`, `04041`, `06258` and `06550`, all `#assume`). Each
  builds an interval of `3..2147483647`, `7..2147483647` or `21..2147483647`: a function over it
  (`FcnLambdaValue.toFcnRcd` allocates `new Value[sz]` for its domain and its values before it
  applies the body) or a quantifier, CHOOSE or set map that enumerates it in normalized order
  (`EnumerableValue.elements(Ordering.NORMALIZED)`, which builds it with `IntervalValue.toSetEnum`:
  `new Value[size()]` and one `IntValue` per element). Arrays of 2^31 - 21 to 2^31 - 3 elements are
  within HotSpot's limit and take about 8.6 GB each, so `TLC.process` catches the OutOfMemoryError
  and prints `Java ran out of memory` (1001, exit 255) at any heap below roughly 9 to 43 GB, and
  TLC's own result above. The jar printed 1001 within 4 s at each heap it was run at (512 MB to 8
  GB, Parallel and G1, with and without compressed references, `-Xss16m`); the same expressions with
  the interval cut to 60,000,000 elements print 1001 at `-Xmx256m` and TLC's own error (`In applying
  the function ...`, `CHOOSE x \in S: P, but no element of S satisfied P`, ...) at `-Xmx3g`. The
  upstream suite files record 1001, which is what the jar prints at the corpus's `-Xmx3g`. Matching
  them would mean printing that Java ran out of memory for a value Prove It can compute, as a
  function of a heap it doesn't have; tla-ts tags them as TLC bugs and checks the unbounded-heap
  output instead. The engine builds no interval of 10,000,000 elements or more, and the trace
  evaluator none of 2^24 or more (`MAXIMUM_INTERVAL`), both far below where a 3 GB heap fails (`\E x
  \in 1..N : x = 0` answers at N = 100,000,000 and runs out of memory at 125,000,000), so an answer
  never depends on TLC's heap. The `heap-dependent-*` startup fixtures keep two of these shapes
  declined, with the jar's output at 3 GB beside them.
- The JVM's array limit (5 runs, `random_02309`, `02420`, `03226` and `07052`, over
  `1..2147483647`, and `random_05311`, over `2..2147483647`, all `#assume`). The same
  allocations of 2^31 - 2 elements or more are ones HotSpot refuses at any heap (`Requested array
  size exceeds VM limit`, an OutOfMemoryError), so TLC prints 1001 (exit 255) whatever the heap,
  as the upstream suite files record. These are deterministic, not unreproducible: they decline
  because the engine doesn't model the array limit ("an interval too large to build"), and they
  aren't in `unreachable.json`. Outside the assumption context the
  jar words the same failure as `1000:1 Requested array size exceeds VM limit` (a function over
  `1..2147483647` in an initial predicate), where a heap failure prints `Java heap space`.
- Wall clock (`tlc/errors/TLC_POSTCONDITION_EVALUATION_ERROR/unknown_stats_key`). Its error
  prints the whole `TLCGet("stats")` record, whose `duration` is `(System.currentTimeMillis() -
  startTime) / 1000L` (`AbstractChecker.getStatistics`). The recorded output says 1; 5 reruns of
  the jar under load printed 1, 4 more printed 3, 1, 2 and 2, and it printed 2, 3, 4 and 6
  when frozen for 1, 2, 3 and 5 s. It declines ("a postcondition that shows how long TLC ran", see
  `TLCGet("stats").duration` above); main prints 0.
- The call stack after a StackOverflowError (`tlc/checker/errors/nonterminal_constant_recursion`).
  The replay of a failed initial predicate (`ModelChecker.doInit` with a `CallStackTool`) pushes
  each node it evaluates and pops it in a `finally` block, which doesn't catch
  StackOverflowError; a pop that itself overflows on the way out leaves its entry, and
  `CallStack.toString` prints the outermost entries left. How many are left depends on the stack
  size and on which frames the JIT compiled. The upstream suite file records `The error call
  stack is empty.`, and the jar sometimes prints one position instead: it printed the one position
  in 1 of 11 runs at the corpus's settings (`-Xmx3g -Xss2m`), 3 of 13 in another series, and 2 of
  20 over stack sizes from 256 KB to 16 MB, the interpreter only, C1 only and no tiered
  compilation, and the empty stack otherwise. tla-ts always prints the empty stack. It declines
  ("recursion too deep"), as the `stack-overflow-call-stack-varies` startup fixture keeps it.

The same unwinding makes every StackOverflowError TLC replays with its call stack vary, though
the jar usually prints the empty call stack the upstream suite files record; these runs are in
`unreachable.json` too, with their counts. Over 27 runs at the corpus's settings, the empty call
stack of `stack_overflow_constraint` came 24 times, and of `infinite_operator_recursion` 10, 9 and
11 times of 12 in its initial predicate, invariant and property; at `-Xss8m`,
`stack_overflow_init` and `stack_overflow_in_invariant_records_error` printed a position in 9
runs of 10, and `infinite_function_recursion`, empty in all 52 runs at the corpus's settings and
the usual variants, printed one in 6 of 240 runs over stack sizes of 256 KB to 32 MB and four
compiler modes. At `-Xss16m` DFID's `stack_overflow` printed an extra `Progress(-1)` line, as the
search ran past the 3 s TLC waits before its first progress report (`AbstractChecker.runTLC`);
at the corpus's settings it printed the recorded output in 27 of 27 runs, and it no longer
declines (see "Depth-first iterative deepening"). The StackOverflowError runs that print no call
stack (the assumption, the next-state relation and an invariant past the initial states) printed
the recorded output in all 20 runs. Those that print a call stack decline ("recursion too deep
... as it computes the initial states"). Of those that print none, an action
constraint TLC computed as it started (`stack_overflow_action_constraint`, `Con == F(0) = 0`) no
longer declines: TLC swallows the StackOverflowError as it computes its constants (a `Throwable`)
and keeps the definition as an operator. So the engine no longer stops where a constant the
configuration names recurses past its depth: it counts the definition as not holding and evaluates
it where it is used, and it stops there again. The evaluator of failures then finds whether the
recursion ends, and TLC reports the overflow on the first successor with the trace to the initial
state (1005, exit 255). A recursion that ends past the engine's depth still declines ("a recursion
too deep that may end"), and so does one that several workers race to report.

One run is deterministic and recorded, but slow on the JVM: `random_08023#assume` walks a filter
of `2..2147483647` lazily, once as TLC computes the definition at startup and once in the
assumption, and printed the Times cast error (2105, then 2154; exit 10) that its upstream suite
file records in 3 of 3 runs, after 8 to 11 minutes, past the corpus harness's 120 s limit. A
checker that walks 2^31 elements faster could match it; Prove It declines
("an interval too large to build"), and it isn't in `unreachable.json`.

The rest of the declines don't vary: every other declined run, rerun on the pinned jar at the
corpus's settings and again with a 1 GB heap, a 1 MB stack, G1, C1 only and random identity
hashes (`-XX:hashCode=0`), printed its recorded output both times, but for one that ran out of
time. `random_07533#assume` walks a filter of `1..2147483647` lazily and prints `{}`: 156 s at
the corpus's settings under load and more than 300 s with C1 only, against the corpus's
120 s limit, so whether its output is recorded at all depends on the machine's speed, though what
it prints doesn't (`random_06973#assume`, 57 and 107 s, is the next slowest). The simulation
whose violation races its worker (`simulate_invariant_form_violated`, `num=8`) printed the
recorded counts in 16 of 16 runs, on one CPU, interpreted and with C1 only.

A simulation's successor that its action leaves a variable unassigned in is reported as
`SimulationWorker.addElement` throws it (2109, with the trace to the successor, a variable it
lacks printed as null, exit 75) where it is in the last trace `-simulate num=` asks for. Before
the last trace, the worker queues the error and goes on to its next trace while the main thread
prints, so the counts TLC prints race it: on `continue_nonfatal_error_then_error`'s spec, `num=2`
printed 2 traces in 4 of 4 runs, `num=50` printed 50 in 3 of 3, and `num=1000` printed 172, 222
and 221. Such a run declines (`a failure before the last trace, whose counts race TLC's worker`).

#### Decline reasons the sections above don't name

Each of these declines exactly the shape it names; the reason is printed after `prove-it: not
native yet:` and, where the engine or a replay meets it, after its prefix (`the engine stopped:`,
`evaluating the failure again:`, ...).

- The replay that evaluates a failure again to print TLC's call stack (`evaluating the failure
  again:`) doesn't follow two kinds of frame, outside an assumption, where TLC prints none, and
  declines there. SubBag of a value that isn't a function fails, as TLC evaluates Bags.tla's
  definition, inside that definition's frames, which the replay doesn't record (`EXTENDS Bags`,
  `SubBag(1) = {}` under init, next, an invariant or a property: "the frames of a standard
  module's definition"). A failure building a function a definition or a LET defines
  (`f[x \in S] == ...`), which TLC builds in the definition's frame, declines alike ("building a
  function a definition defines").

- A TLCGet("spec") record a failure prints whole (`Attempted to select nonexistent field
  "properties" from the record [ inits |-> ..., actions |-> ..., temporals |-> ..., invariants |->
  ..., impliedinits |-> ..., impliedtemporals |-> ..., variables |-> ..., actionconstraints |->
  ..., constraints |-> ..., impliedactions |-> ... ]`) shows TLC's fields in the order of the
  HashMap TLC builds it from, which the binary's normalized record doesn't keep, so that failure
  declines ("selected a field TLCGet("spec")'s record lacks, which TLC prints in its own order");
  main prints the wrong order without -inv and -invlevel, and declines with them.

- DFID (`-dfid N`): `DFID with _POSSIBLE predicates`, `DFID with TLCGet of diameter or distinct`,
  `DFID with random draws, register writes, or JSON files`, `DFID with effects, liveness,
  continuation, or output files`, `DFID initial-state order can affect the search`, `a DFID
  incomplete successor`, `a DFID action evaluation failure`, `a DFID invariant evaluation
  failure`, `a DFID next-state failure`, `a DFID violation`, `a DFID violation or evaluation
  error`, `DFID effects while generating several successors`, `DFID worker chooses among multiple
  states`, `DFID depth limit reached before reporting completion`, the `DFID ... trace` and `DFID
  initial ... failure` reasons, `a DFID trace under -continue`, the `DFID action ...` reasons of
  the failure's replay, and `DFID is not requested through this host` (the library's host). Each
  is a part of TLC's `DFIDModelChecker` the search doesn't follow; see "Depth-first iterative
  deepening". Among the `DFID ...` reasons, by name: `DFID of a spec that applies _Track`;
  the engine's `DFID action failure trace`, `DFID invariant failure`, `DFID invariant failure
  trace`, `DFID next-state failure trace` and `DFID violation trace`, where it can't rebuild the
  trace; and the report's `DFID initial failure has an unrenderable value`, `DFID initial failure
  has no invariant`, `DFID initial invariant exception cannot be reported exactly`, `DFID initial
  failure state is missing`, `DFID action failure trace has an unrenderable value`, `DFID action
  failure has no property`, `DFID action failure in an instance scope`, `DFID action failure has
  no reproducible call stack`, `DFID next-state exception cannot be reported exactly` and `DFID
  incomplete successor has no missing variable`. `unsupported DFID violation` is a violation of a kind the DFID report doesn't word
  (one other than an invariant's violation or failure, a deadlock or an action property's
violation).
- The generator (`-generate`): `a generated walk without the worker's generator`, where a walk
  that draws a disjunct or a stride as TLC's generator does (`rng.nextDouble`, `rng.nextPrime`)
  finds no generator of the worker to draw from.
- The evaluator of failures: `a constant definition with parameters`, where the replay is asked
  to compute as TLC starts (`processConstantDefns`) a definition that takes parameters, which TLC
  never computes there; `evaluating the failure again: a VIEW the model doesn't
  define`, of a failure TLC met in the VIEW of an initial state; and `<what>: a message that
  prints a value TLC never initialized`, a failure whose message prints a value TLC never initialized, a
  THEOREM's or an ASSUME's of an INSTANCE, whose `toString` throws a NullPointerException with a
  text that depends on the class holding it, where the evaluator writes `null`.
- _Track (see "_Track, _Counts, _CheckName and _PrintCounts"), the engine's reasons: `_Track`
  (where the context can't print), `_Track on several workers`, `_Track in a spec that reads or
  sets registers otherwise`, `_Track of constants, which TLC may compute as it starts`, `a _Track
  condition that isn't a boolean`, `_Track of a name that isn't a string`, `_Track of a register
  set otherwise` and `_Track of a count past an int`; and a POSTCONDITION's, reading `_Counts`:
  `reading _POSSIBLE's counts and _Track's at once`, `reading a register _Track set that isn't a
  function`, `reading a count _Track took of a name that isn't a string`, `reading a count _Track
  took of a name TLC made as it searched`, `reading a count _Track took that isn't an integer`
  and `reading counts _Track took in a crowded bucket`.
- A `tlc2.overrides.TLCOverrides` index (see "Java overrides that stay declined"): `a TLCOverrides
  index whose classes the front end doesn't read`, and `a class a TLCOverrides index names` `that
  isn't a plain class`, `with a superclass`, `that implements an interface`, `with a static
  initializer that Class.forName runs` (which TLC runs as it loads the class) or `with a method
  TLC reports` (an annotation TLC warns of, or one without its module or name).
- Warshall (`TransitiveClosure`): `Warshall of a relation that may have an effect`, `Warshall of a
  function TLC keeps lazy` and `Warshall of an endpoint TLC may fail to fingerprint`. TLC's Java
  method sizes the relation, converts each element with `toTuple` and numbers the endpoints by
  their fingerprints, which an effect or a lazy function would show in another order.
- Operator tables a configuration assigns (`OpRcdValue`): `a value of an operator's table the IR
  can't hold`, `an operator table without an argument tuple`, `an operator's table applied to the
  wrong number of arguments` (TLC: "Attempted to apply the operator ... with wrong number of
  arguments."), `an operator applied to the wrong number of arguments`, and `an INSTANCE fact
  literal TLC did not initialize`, a literal of an INSTANCE's substitution TLC reads before its
  `initialize`.
- Random draws: `RandomSubsetSet of a count that isn't a natural number`, `RandomSetOfSubsets of
  an average that isn't a natural number`, `RandomSubsetSet of a probability that isn't a string`,
  `RandomSubsetSet of a string that isn't a probability` (`Double.valueOf` outside 0 to 1),
  `RandomSubsetSet of a value that isn't a finite set`, `RandomSubsetSet of a value with untracked
  lazy normalization`, `RandomSubsetSet of a count greater than the number of subsets`,
  `RandomSetOfSubsets of an average larger than the base cardinality`, `RandomElement of a value
  that isn't a finite set` and `RandomSetOfSubsets without default Java method origin`: the
  failures of `Randomization`'s Java methods, whose messages and draws the engine leaves to TLC.
- Json (`Json`, `ToJson*`): `a Json operator's file with a lone surrogate`, `a Json conversion
  whose nested key order was not retained`, `a Json conversion whose record fields were not
  retained`, `a Json conversion of an unsupported physical input class`, `a Json conversion whose
  physical input class was not retained`, `a Json conversion whose record subtype was not
  retained`, `a Json conversion without a proved standard source prefix`, `a Json operator's
  record, whose fields TLC writes as it holds them`, `ToJson of a text the engine made unranked`,
  `ToJson of a value nested too deeply for the JSON writer`, `ToJson of a string with a lone
  surrogate`, `JSON that TLC's Json module fails to parse` (`JsonParser.parseReader`), `a JSON
  value TLC's Json module fails to convert` (`Json.getValue`: null, or a number that isn't a
  32-bit integer), and `JSON that starts with two byte order marks`. TLC's conversion follows the
  Java class the value has (`RecordValue`, `FcnRcdValue`, `TupleValue`, ...), and its order of
  fields, where the engine holds the value without that class. `a constant definition with
  effects applying a Json operator, which TLC computes as it starts`: TLC computes it as it
  starts, the engine only where it is used (see the startup definitions above).
- `a standard module that uses a module a file of the user's replaces`: a file of the user's
  named like a standard module (`Json.tla`, `TLC.tla`) beside the spec, which TLC loads in place
  of its own, where a standard module the spec reads, other than TLC, Sequences, FiniteSets and
  Randomization, whose operators are all Java methods, extends it (for TLCExt, a user's TLC,
  Integers or Naturals).
- `a definition the configuration names whose body a module-scoped substitution replaces`: a
  name the configuration selects or substitutes for another, whose definition `K <- [M] Q`
  replaces, where TLC evaluates K's own body but other parts read Q, where a definition TLC
  computes as it starts that names K has an effect, or where TLC fails to cast a literal body's
  substitute.
- `a substitution whose target is an INSTANCE's copy of a definition with a module-scoped
  table`: `K <- A` where A is a copy an INSTANCE with substitutions makes of a definition with an
  entry `A(0) = [M] 7`, whose body TLC's substitution evaluates as written, and something may
  read K or the copy's body has an effect; see "Scoped configuration entries".
- `module-scoped tables of more than one module that TLC fails to build`: TLC reports the first
  failing module in its Hashtable's order.
- ANY (`AnySet`): `isEmpty of ANY`, `size of ANY`, `comparing ANY`, `ANY membership without its
  normalization phase` and `eagerly normalizing a set containing ANY`. TLC's `AnySet.ANY` can't be
  compared, sized or fingerprinted, and fails in the method that tries.
- TLC's registers: `TLCSet of a key that isn't a natural number` (`TLCGetSet.TLCSet` takes no
  other string but "exit", "pause" and `-D` names). `TLCSet("pause", TRUE)` prints `Press enter to
  resume model checking.` and reads a byte of the standard input where TLC's checker is the
  breadth-first `ModelChecker`: the binary does so with one worker from the initial predicate on;
  in a simulation, which has no model checker, it does nothing. Elsewhere (several workers, DFID,
  the assumptions, the library's interpreter) it still stops the engine (`TLCSet of a key that
  stops or configures TLC`).
- Lazy values and effects: `a warning in a finite function TLC keeps lazy`, `a LET definition
  with effects, named more than once, held in parts`, `a LET definition with effects TLC keeps as
  a lazy function`, `a tuple or a record of several arguments that print`, `a set of functions,
  records or tuples of parts that print` (TLC evaluates the parts once each as it builds the set,
  where its membership test and enumeration evaluate them apart), `IOUtils's Serialize of options
  that print` (TLC evaluates the options again as it reads them), `the default formatting of a
  lazy @@ argument` (`CombineFcn` of a value TLC formats otherwise than the evaluator, but a
  function TLC keeps lazy, or a set of functions, records or tuples, of parts that are set
  enumerations, intervals, Nat, Int, Real or STRING, one of them TLC's overridden set, which
  `toString` fails to size and prints unexpanded), `a
  constant definition whose filter enumeration fails after printing`, `a mixed scalar set tested
  against an infinite set`, and `a tuple pattern with an ambiguous physical class`.
- Failures the engine words: `EXCEPT on a non-function`, `a temporal formula in a
  state` (`~>` or `-+->` that TLC evaluates in `Tool#evalAppl`), `comparing Seq(S) with a value
  the engine doesn't`, `constructed a set with too many elements` (`TLCGlobals.setBound`), and
  `computing an AssertError` with the reason the replay gives (`an AssertError with effects`, `an
  AssertError that isn't a boolean`, `an AssertError that fails`).
- The trace evaluator's replays: `Trace with an unproven Java method origin` (TLC's `Trace` read
  where a Java class of the user's may replace it), `a failure comparing the sets a set TLC keeps
  lazy is built of` (the ranges of two `Seq(S)` and the parts of a lazy set, which TLC compares
  in a place the evaluator doesn't hold), `a FingerprintException the replay throws`, `an action
  property whose box action has no place` and `... has two places`, `an action property the model
  doesn't have`, `an invariant the model doesn't have`, `a constraint the model doesn't have`,
  `replaying the expansion: an action property that doesn't fail again`, and, under `evaluating
  the failure again:`, `an invariant is violated`, `an action property without a step`, `an
  earlier action property is violated`, `a check before the action property prints` and `a set
  TLC fails to normalize as it words a failure, in a fingerprint stack` (`SetEnumValue`'s
  `getNewHead` adds the set's source, which the evaluator doesn't hold).
- ALIAS and dumps: `record with a _format field`, `of a set TLC fails to normalize as it prints
  it`, `function of no keys`, `of a model with an ALIAS`, `whose ALIAS output has not been
  retained by its caller`, `a null literal in a trace dump` and `a null literal in an encoded
  value`.
- POSTCONDITION: `a postcondition reading counts past an int` (or `a count`), `a postcondition
  that shows how long TLC ran` (a print or a failure that shows the duration, as the run's whole
  `TLCGet("stats")` record) and, before the run, `a postcondition that may read how long TLC
  ran` (see `TLCGet("stats").duration` above).
- `a Java method argument that isn't an integer`: the trace evaluator's wording of an Integers
  or Naturals method that TLC's Java class takes as `IntValue`, applied to a value of another
  class, where it can't name that class as TLC's cast failure does (`Cannot cast
  tlc2.value.impl.X to tlc2.value.impl.IntValue`).
- `a function over an interval too large to build`: the trace evaluator builds a function over
  an interval, which TLC may keep lazy (`FcnLambdaValue`) and apply at a few arguments only; one
  whose interval has as many elements as the evaluator builds an interval to (`MAXIMUM_INTERVAL`)
  or more declines (the "interval too large to build" above is the interval itself).
- `IOUtils's Serialize, which TLC writes or fails at`: the engine meets IOUtils's Serialize of the
  NDJSON format, or of options whose format isn't a string, which TLC writes or fails at in
  `Json.textSerialize`, and hands the check to the evaluator of failures (see "JSON conversion"
  above); where that evaluator doesn't follow it either, the run declines with this reason.
- How a reason is built: the engine's stops and the replays' reasons are joined with `: `, the
  outermost first. `the engine stopped: X: Y` is a failure the search met, where X is the
  engine's own name for it (`division by zero`, `applied a function outside its domain`, `a
  mistyped membership in Nat`, `a predicate that isn't a boolean`, `an invariant violated in an
  initial state`, `applied a recursive function outside its domain` and the rest of the list in
  `search.rs`), which is no decline by itself, and Y is why the replay that words it as TLC
  declined. `the engine declined: Y` is a shape the engine doesn't follow, and `the engine
  declined: a startup definition that fails: rebuilding a trace: a startup definition the search
  found failing that the evaluator can't follow: Y` one TLC computes as it starts, where Y is the
  evaluator's reason. `an assumption that fails to evaluate: evaluating the assumption again: Y`
  is the replay of a failing assumption; Y may itself be `a startup definition that failed where
  TLC may fail otherwise: Z`, with the replay's reason Z.
- The command line (each an option TLC follows that the binary doesn't model, or an order of its
  effects it doesn't): `the TLC option <option>` (`-maxSetSize` of a valid bound, `-loadTrace` and
  the rest of the options `args.rs` names), `-simulate <setting>` (`stats=basic`, `stats=full`,
  `sched=rl`, `sched=rlaction`, `file=...`; a `file=` whose number of traces an earlier
  `-simulate num=` gave, which `TLC.traceNum` keeps across options, declines too, where the binary
  had reported that no `num` was given), `-invlevel <level>` (a level that isn't plain digits,
  as `-1`, which TLC pastes as written into an expression of its own), `-suppressMessages <code>`
  and `-messagesAsErrors <code>` (a code whose message the binary doesn't control, as `2143`),
  `-checkpoint <minutes>`, `several codes both suppressed and made errors` (TLC names them in a
  HashSet's order), `an error in the command line after -fpmem's notice` and `-fpmem's notice with
  several specifications` (TLC prints the notice of an absolute `-fpmem` as it reads the option),
  `-userFile before an option TLC stops at` and `-userFile into a file it can't create` (TLC creates
  the file as it reads the option), `-dump class,` of one of TLC's own `IStateWriter` classes and
  `-dump class, with a class path beyond the jar`, `-dump into the meta directory`, `-dfid with -dump into a file it can't keep`, `-recover with
  -dump` and `-recover from a checkpoint`, `-view with a VIEW`, `-terse with a value TLC may keep
  lazy` (`-terse` keeps TLC from expanding such a value as it prints it, `TLCGlobals.expand`),
  `-continue to a search that stops`, `-continue with temporal properties`, `-continue with a
  POSTCONDITION`, `-difftrace in a simulation`, `-teSpecOutDir into a directory that isn't there`
  and `-teSpecOutDir of a path the binary doesn't model`, `a -postCondition operator TLC may find
  otherwise` (one with arguments, or defined in another module than the one named), and the `-inv`
  reasons: `-inv of an expression that fails to parse` (also `, after the constant definitions`,
  and `, with a configuration failure TLC may report after it`: TLC fails the expression in
  `processConfig` before it processes a CONSTRAINT, ACTION_CONSTRAINT, `_RL_REWARD`, `_PERIODIC`
  or `_POSSIBLE` and before it reads a SYMMETRY or VIEW, so where the configuration names one of
  them, a configuration failure past SANY's declines, but for a missing constant's and the
  specification's, the properties' and the invariants' names and arity),
  `-inv beside a Java override TLC loads` (TLC reports the override's loading again as it
  processes each expression's module, `TLCDebuggerExpression.process`),
  `-inv in a module whose end the binary doesn't place` and `-inv of an expression the IR spreads`,
  where TLC parses the expression into a module of its own. An expression that names an operator
  SANY doesn't know, where the root module links without it, fails that module's generator
  (`TLCDebuggerExpression.process`), which TLC reports as it reports one that fails to parse,
  with `Semantic error while parsing breakpoint expression` after SANY's location `Unknown
  location`; the expression's other semantic and level errors still decline (`an error tla-front
  raises that TLC reports without a code`), and so does one of several -inv expressions
  (`-inv of several expressions, one of which SANY rejects`).
- The front end: `SANY's report of <what>`, a module the front end doesn't report on as SANY does:
  `a module SANY's parser accepts` (where the front end's parser doesn't) and `a module of the
  CommunityModules TLC's jar bundles` (which the front end doesn't have), `configuration values TLC
  can't compare` (TLC sorts a configuration's set values with `compareTo`), `warnings about the
  invariants or properties with a symmetry` (TLC warns as it computes the symmetry, between the
  constant definitions and these warnings), `<what fails>, which the constant evaluator doesn't
  compute` (as `an expression` or `arithmetic on a value that isn't an integer`: a constant formula
  of a temporal property whose failure TLC reports as it checks it), and `the name <name>`, a name
  the engine or the evaluator doesn't resolve (as a constant a configuration assigns an operator's
  table to).
- The simulator (`-simulate`): `a simulation on several workers`, `a simulation that checks
  temporal properties with a POSTCONDITION, a VIEW, registers or random draws`, `a simulated
  behavior that violates the temporal properties: <why>`, where the counterexample can't be
  printed as TLC prints it (`<why>` is `a POSTCONDITION or an ALIAS`, `a step whose action the
  trace lacks`, `the label of an initial predicate`, `a property the IR doesn't name`, `a
  simulated behavior printed through an ALIAS that prints`, or the reasons of the states' texts,
  as `a record of several fields, which TLC may or may not have sorted`), `a simulation with a POSTCONDITION, an ALIAS, registers, random draws or
  an unbounded depth` (TLC checks the postconditions with the simulator's own statistics),
  `a simulation with -dumpTrace, whose postcondition TLC's simulator checks`, `a simulation with
  a _POSSIBLE predicate`, `a simulation that applies _Track`, `a simulation whose ALIAS may read
  TLCExt's Trace` (the simulator's Trace gives each record its state's action too), `a
  simulation's POSTCONDITION: <reason>` (the postcondition evaluator's
  reason, as `a postcondition: TLCGet of a key a simulation reads otherwise`), `a configuration
  error of a simulation with a POSTCONDITION, which TLC may report after it simulates`, `a
  failure in a simulation with a POSTCONDITION, which TLC checks of its trace`, `a failure
  evaluating the model in a simulation: <reason>`, `a constant POSTCONDITION after an initial
  state's violation`, `a postcondition the model doesn't define`, `a simulation's violation under
  -continue` (TLC reports it and goes on generating traces), `a simulation's violation before its
  last trace, whose counts race TLC's worker` (the worker goes on as the main thread prints), `a
  simulation of a temporal formula TLC rejects` (TLC rejects it only as it checks a trace), `no
  initial state`, `no initial state in the model` and `a successor that isn't complete` under
  -generate (the simulator's reports of these, which differ from the model checker's; an initial
  state that isn't complete is reported as `Simulator.simulate` does, once it has counted the
  initial states and checked those before it, except where TLC writes its trace exploration spec:
  `a simulation's incomplete initial state with unrenderable values or trace files`, and `a
  simulation's incomplete initial state has an unrenderable value`, a value of it the store
  can't give back), `an incomplete successor in a simulation: <reason>` (`the trace files of the
  behavior`, `an ALIAS of a state that lacks a variable`, `the error state of an unbounded
  behavior` under -depth -1, where TLC prints the error state alone, `a failure before the last
  trace, whose counts race TLC's worker`, `a state whose values TLC may hold otherwise than the
  engine`, and the replay's checks that the behavior is the one that failed: `a trace without
  states`, `an action the IR lacks`, `a successor of another action than the one that failed`
  and `a successor that lacks no variable`), the reasons of `a failure evaluating the model in a
  simulation: <reason>` (`the trace exploration spec's postcondition, which TLC checks of it`, `a
  model that reads the statistics or registers of the run`, where TLC's message may write a value
  of the run it holds as an empty record, `a model that sets registers or draws at random`, which
  evaluating the failure again doesn't follow, `a successor's check that fails before the last
  trace, whose counts race TLC's worker`, `an initial state the failure lacks`, `a name the IR
  doesn't carry`, `an action property the model doesn't have`, `a site TLC's simulator doesn't
  fail at`, `a failure whose code TLC exits by otherwise`, `the label of an initial predicate`, `a
  step whose action the trace lacks`, `a simulated behavior printed through an ALIAS that prints`
  and `a record of several fields, which TLC may or may not have sorted`), `TLCGet of a key a simulation reads otherwise` and `TLCGet of a simulation's run
  where its empty records may matter` (`Simulator.getStatistics` and its trace statistics),
  `TLCGet of a trace's count in a simulation without end` (TLCGet("diameter") or
  TLCGet("stats") read as the worker runs with no `num=`: each trace's count would be an integer
  the store keeps for good, where TLC's simulator runs in constant memory),
  `TLCGet("action") of an action the simulation doesn't record`, `a simulation's statistics past
  an int`, `an action the simulation doesn't name`, and, under `evaluating the simulation's
  failure again:`, `a site the simulator doesn't fail at`, `an initial state the initial
  predicate doesn't give`, `an earlier constraint doesn't hold`, `a successor without a step`, `a
  failure that prints` and `a set TLC leaves unnormalized, or a state it can't complete`.
- Coverage (`-coverage`): `coverage of a model with <what>` (`temporal properties`, `properties
  TLC checks as invariants or actions`, `a POSTCONDITION`, ...), `coverage on more than one worker
  is timing-dependent in TLC`, `a set filter TLC keeps lazy (SetPredValue)` and `the builtin
  <name>, which TLC may not override in Java`: TLC counts the evaluations of each expression,
  which these change.
- The model checker's report: `a POSTCONDITION TLC rejects after temporal properties, _POSSIBLE or
  under -continue` (TLC fails on a POSTCONDITION it rejects as it comes to check them, with an
  unexpected exception, then reports the statistics, which the binary follows only without
  these), `a POSTCONDITION that reads the run or writes a trace file after
  an initial state's violation`, `a POSTCONDITION that reads the run after an incomplete initial
  state`, `a POSTCONDITION TLC rejects after an initial state's violation`
  and `DFID's initial violation with a POSTCONDITION` (TLC checks the postconditions then, on the
  CounterExample of the state and with the initial states' counts, and keeps the violation's exit
  status, which the binary now follows where the postconditions read neither the counts nor the
  registers; DFIDModelChecker checks none), `a POSTCONDITION after a failure that reads TLC's CounterExample`
  (after a failure TLC's worker checks the postconditions on a CounterExample it builds once it
  has stopped, with a third field, `console |-> FALSE`, whose name TLC interns only as it builds
  it; what the postconditions print otherwise comes after the trace, before the report of one
  that fails and the call stack), `a failure with a POSTCONDITION in a
  spec that prints` (TLC rebuilds the trace again for the postconditions, between its prints), `a
  POSTCONDITION of a spec without variables that names a next-state relation`, `a postcondition:
  <reason>` (the postcondition evaluator's failure without a message TLC would print, as
  `TLCGet` of a key the run doesn't hold), `a postcondition of an action whose parameters its
  scope doesn't bind`, `a _POSSIBLE predicate the search didn't witness: <reason>` (see "A
  _POSSIBLE predicate the search didn't witness"), `the assumptions printing other than TLC
  prints`, `an ALIAS record with a _format field` (TLC formats the state with it), `a symmetry
  function of values that aren't model values` (where some function may be one TLC builds over an
  interval, whose missing domain array `MVPerms.permutationSubgroup` fails on otherwise; a
  symmetry of `Permutations`, `:>` and `@@` functions reports TLC's own exception), `a
  symmetry value that isn't a function`, and `warnings about the configuration before a symmetry
  that may print` (TLC prints its warnings about the configuration, such as a state-level
  PROPERTY's, as it processes it, before it computes the symmetry; the binary prints them there
  once the configuration's predicates hold, but reports what the symmetry's definition prints
  with the constant definitions' prints). A constant declared without parameters that the
  configuration defines by a table (`CONSTANT N(1) = 2`) fails where it is read as
  `OpRcdValue.eval` does, applied to no arguments.
- The engine's shapes: `a recursive function over a tuple pattern`, `a recursive higher-order
  operator`, `a failing argument of a recursive operator that prints` (TLC evaluates an argument
  where the body first reads it, after what the body printed before, and the engine before the
  body), `a recursion that prints, deeper than TLC's stack surely holds` (past 50 nested calls,
  where TLC's stack, which depends on its thread and on the frames each level takes, may overflow
  after printing part of what the engine prints: `R(n) == IF n = 0 THEN 0 ELSE P(n, n) + R(n -
  1)` overflowed at about 640 levels as TLC computed its constants), `expression Enabled` (ENABLED under a prime), `a CASE TLC fails to generate from`
  and `generating from a disjunction of unknown nesting` (TLC's generator throws an
  UnsupportedOperationException at a CASE), `TLCCache of an expression that reads variables`,
  `TLCGetAndSet of a key that stops or configures TLC`, `PickSuccessor with temporal properties`,
  `PickSuccessor under a VIEW or SYMMETRY`, `PickSuccessor, which asks TLC's user` (a FALSE
  condition makes TLC read its standard input), `a PickSuccessor condition that isn't a boolean`,
  `PickSuccessor of a successor TLC fingerprints incomplete`, `IsABag of a function TLC keeps
  lazy` (TLC fails to enumerate its domain), `an empty JSON object, which TLC holds apart from
  <<>>` (TLC reads `{}` as an empty record, which the store holds as the empty sequence),
  `writing an empty sequence that may be TLC's empty record`, `enumerated ANY` and `fingerprinting
  ANY`, `TestRandomSetOfSubsets`, `TestRandomSetOfSubsets of an argument with effects`,
  `TestRandomSetOfSubsets where TLC may keep its function lazy`, `TestRandomSetOfSubsets applied
  outside its domain` (`FcnLambdaValue.apply` outside 1..5 prints the whole function, drawing it)
  and `TestRandomSetOfSubsets without default Java method origin`, `TLCEvalDefinition of a
  definition it is written in`, `TLCEvalDefinition of a name the front end didn't look up`,
  `TLCSet of a system property to a value whose text depends on how TLC built it`,
  `TLCSet("exit", TRUE) outside an invariant with several workers`, `comparing a set TLC builds
  past TLCGlobals.setBound elements` and `a set TLC keeps lazy past TLCGlobals.setBound elements,
  held in a value` (see "Sets past `TLCGlobals.setBound`"), `IOUtils's Serialize of a file that
  can't be read before it is written` and `IOUtils's Serialize that fails to write`, `a Json
  operator's file that can't be read before it is written` (`JsonSerialize` and
  `ndJsonSerialize`), each where the file can't be read, is a chain of more than 40 symbolic
  links, or is written outside a check's journal, and `the builtin <name>, whose value the interpreter
  computes` or `, which the TypeScript engine runs in the interpreter`.
- The trace evaluator's values and methods, each a place where TLC's Java class of a value, or
  its order of evaluation, shows and the evaluator doesn't hold it: `built a function over an
  infinite set` and `made a tuple of a function over an infinite set` (`FcnLambdaValue.toFcnRcd`
  and `toTuple` of a domain that isn't an overridden set), `a lazy value taken as a tuple`, `a
  tuple pattern whose TLC value class is unknown`, `a tuple cast whose TLC value class is
  unknown`, `a tuple pattern applied to a tuple of another length` (`apply` returns null),
  `CHOOSE of a tuple pattern over a lazy value`, `DOMAIN of a lazy function of several parameters
  or a tuple pattern`, `an EXCEPT of a lazy function of several parameters or a tuple pattern`,
  `an EXCEPT of a lazy function past its first key`, `a failing test of a lazy function's domain
  TLC built from an expression` (TLC reports it as a value it can't fingerprint), `warning in a
  function body TLC keeps lazy until application`, `the domain of a constructor in an argument,
  printed`, `compared a function TLC keeps lazy with a function of an unknown class`, `IsFiniteSet
  of a function the evaluator doesn't know TLC built`, `a lazy set whose conversion's deep
  normalization the evaluator doesn't follow`, `a lazy set whose expansion fails to print, which
  TLC swallows: <reason>`, `a print whose normalization changed as it settled`, `PrintT of SUBSET
  of a function of 7 keys or more` (TLC prints it as written), `a lazy filter's predicate that
  isn't a boolean`, `a lazy filter's element that isn't a tuple of its names`, `a lazy filter's
  membership outside the evaluator`, `an EvalException that a filter's membership rewords`
  (`SetPredValue.member` words it as its own failure), `selected a field a record holding a null
  lacks` and `applied a record at a field TLC never initialized` (TLC's NullPointerException
  printing the record), `a failure within another Java method's caught FingerprintException`,
  `a startup print the search couldn't compute that fails here`, `a startup definition the
  search failed at a limit of that the evaluator can't follow: <reason>` and `... that warns or
  prints here`, `a constant definition TLC computed at startup with effects, applied`, `a
  FingerprintException in a startup definition that failed` and `a variable assigned a startup
  definition that failed in a way the evaluator can't word, which TLC may report as a state it
  fails to fingerprint` (TLC evaluates such a definition again with the sources of its use),
  `TLCGet("config") without the run's workers`, `TLCEvalDefinition of a value that isn't a
  string`, `TLCEval of a value holding a set TLC can't normalize, in 1.7.4`, `RandomSubsetSet
  after effects in a function TLC keeps lazy`, `RandomElement of an empty set TLC may draw null
  from` (a set built with room draws null), `Trace reconstructs a worker prefix with unfollowed
  effects`, `ToTrace of a CounterExample without states`, `ToTrace of a value whose
  CounterExample origin was not retained`, `ToTrace of a trace missing a state`, `the builtin
  <name>` (a method the evaluator doesn't compute, as TLCGetAndSet, TLCGetOrDefault or a
  Sequences method a module of the user's binds with another arity, `Append@Sequences`),
  `JsonDeserialize, whose file the replay doesn't read or write` (and the other Json file
  operators), the Bags failures `<operator> of a value that isn't a bag` (as `(-)`) and `SubBag
  of a bag whose counts don't compare`, `expected a set, not a function` (and of other kinds), `a
  mistyped membership in an interval`, `compared an overridden set with another value` and
  `SortSeq of a non-sequence`, each as the replay of a startup definition that failed where TLC
  may fail otherwise.
- Warshall (`TransitiveClosure`), besides those above: `Warshall of a relation whose evaluation
  is not proven`, `Warshall of a relation whose enumeration is not proven`, `Warshall of an
  element the evaluator doesn't follow`, `Warshall of an element the evaluator doesn't take as a
  tuple`, `Warshall of a power set the evaluator doesn't size` (`SubsetValue.size` overflows from
  31 elements), `Warshall of a product the evaluator doesn't size`, `Warshall of a lazy set the
  evaluator doesn't enumerate`, `Warshall of a value the evaluator doesn't hold as TLC does`,
  `Warshall of endpoints TLC may fail to compare`, `Warshall of endpoints the evaluator can't
  tell apart` and `Warshall of an endpoint the evaluator doesn't fingerprint`: TLC's method sizes
  the relation, converts each element with `toTuple` and numbers the endpoints by a Hashtable of
  their fingerprints.
- `@@` (`CombineFcn`): `@@ argument containing a function whose written key order isn't
  retained`, `normalizing an @@ argument whose elements may fail to print` and `the default
  formatting of an @@ argument's function keys`: TLC formats the arguments as it holds them.
- Null values TLC holds where a value was never initialized (an INSTANCE's literal TLC reads
  before its `initialize`, a record's field): `a null tool value used by a consumer the replay
  does not model`, `a null tool value in an unproved sequence conversion`, `a null tool value in
  a cardinality conversion`, `a null integer argument`, `a comparison with a null tool value`, `a
  comparison involving a null tool value`, `an equality involving a nested null tool value`,
  `formatting a comparison with nested null tool values`, `a null literal comparison under a
  different TLC version`, and the `... containing an uninitialized literal` reasons of Json and
  Serialize below: TLC fails with a NullPointerException whose text names Java's variables,
  which the evaluator words only where it knows them. `IsFiniteSet` of a set enumeration written
  in place that holds one answers TRUE: OPCODE_se evaluates the elements in order into a
  `SetEnumValue` it doesn't normalize and `isFinite` reads none (in an assumption, any other
  elements; elsewhere, number, string and boolean literals beside it), as `IsFiniteSet({N!A})`
  with `THEOREM A == c` in a module `N == INSTANCE I WITH c <- 1` instantiates, which main
  matched. A union with it (`{N!A} \cup {1}`) fails in TLC with a NullPointerException and
  declines; a set nesting it, an element that may fail beside it outside an assumption, and a
  definition naming the set decline as before, where main matches. So do other uses main matches
  (see "Declines to win back where main matches"): `DOMAIN [v \in {N!A} |-> 1] = {}`, `{N!A}
  \subseteq {1}`, `({N!A} \cup {}) = {}`, `CHOOSE s \in SUBSET {N!A} : TRUE = {}`,
  `Cardinality({N!A} \cup {N!A}) = 1` and `Len(SelectSeq(<<N!A>>, LAMBDA x : TRUE)) = 1`.
- Json and Serialize, besides those above: `a Json conversion nested too deeply`, `a Json
  conversion whose physical function class was not retained`, `a Json conversion whose physical
  function order was not retained`, `a Json conversion whose physical set class was not
  retained`, `a Json conversion key whose default text was not retained`, `a Json conversion of
  an unsupported value`, `a Json conversion of a string with a lone surrogate`, `a Json
  conversion without its packaged Java implementation`, `a Json operator's failure in a model
  with effects`, `a Json operator's failure with a lone surrogate`, `a Json operator's text with
  a lone surrogate`, `a Json operator's file that Java's File holds otherwise` or `holds
  invalid`, `a Json operator's file that can't be read before it is written`, `a Json operator's
  file that TLC may fail to open`, `a Json operator's file of an unknown physical class`, `a Json
  operator's value of a lazy function`, `formatting a Json operator's value containing an
  uninitialized literal`, `a cast in Serialize of a value whose TLC class is unknown`, `an option
  Serialize's options lack` (also `, of a function TLC converts` and `, printing a nested null`),
  `Serialize of a lazy function`, `formatting Serialize's payload`, `file` or `non-record options
  containing an uninitialized literal`, `Serialize's file with a lone surrogate`, `Serialize's
  file that Java's Paths holds otherwise` (`Paths.get` drops a repeated or final slash), and
  `Serialize's charset with a lone surrogate` and `Serialize's charset, which only decodes`
  (`Files.newBufferedWriter` makes the encoder before it opens the file). TLC's conversion
  follows the value's Java class and order, and its file operators Java's `File` and `Paths`.
- The replays of failures, besides those above: `evaluating the failure again: a successor TLC
  fails to fingerprint with an error it skips finding it again` (see "Known wrong outputs"), `an
  action property whose box action has two places`, and the DFID replay's `DFID action failure
  without a step`, `DFID action property is missing`, `DFID action failure replay did not fail
  without effects`, `DFID action wrapper range is missing` and `DFID action wrapper range is
  ambiguous`.
- DFID, besides the list above: `DFID with coverage`, `DFID with simulation`, `DFID continuation
  with trace files`, `DFID initial invariant failure`, `DFID action failure`, `DFID next-state
  failure` and `DFID trace` `with trace files, random draws, or register writes`, `DFID incomplete
  initial state with unrenderable values or trace files`, `DFID incomplete initial state has an
  unrenderable value`, `DFID incomplete trace holds a value whose printed shape is not retained`,
  `DFID incomplete trace with trace files`, `DFID fingerprint distance is nonpositive`, `DFID
  initial failure with printing: <reason>`, `DFID initial state failure: <reason>` (a failure
  computing the initial states the trace can't word, under -continue, or with an earlier
  violation noted; one in the initial predicate is reported as `DFIDModelChecker.modelCheckImpl`
  does, as an exception it didn't expect, then TLC's `Tool` in place of the call stack, unless
  `DFID initial failure with trace files, a postcondition, random draws, or register writes`, or
  the initial predicate doesn't fail again alone: `evaluating the simulation's failure again:
  <reason>`), `DFID initial invariant failure state`, and `DFID liveness constructor error before a tautology`
  (TLC's DFID checker reports the liveness checker's construction error, 2253, before it rejects
  a tautology).

- Simulation (`-simulate`), besides the sections above: `a simulation under SYMMETRY` (TLC's
  simulator reports and fingerprints its states otherwise under a symmetry), `a simulated
  behavior's temporal properties whose atoms print or read the diameter`, `a simulated behavior's
  temporal properties whose atoms print` and `a simulated behavior's temporal properties the
  checker declines` (`LiveCheck1.checkTrace` of each behavior evaluates the atoms
  as it asks for them, which the engine follows only where they neither print nor read TLC's
  registers, and only where the liveness checker follows the behavior), `a property the IR
  doesn't name`, `a trace whose values TLC may hold otherwise than the engine` and `a state whose
  values TLC may hold otherwise than the engine` (a value whose text depends on the Java class
  TLC built it as, or a record TLC may or may not have sorted), `the trace exploration spec's
  postcondition, which TLC checks of it`, `a successor's check that fails before the last trace,
  whose counts race TLC's worker` (TLC's worker reports such an error and goes on to its next
  trace, so the counts it prints depend on its timing), `a site TLC's simulator doesn't fail at`,
  and `a failure whose code TLC exits by otherwise`.
- SYMMETRY, besides the sections above: `an empty symmetry TLC may not hold as a set
  enumeration` (an empty set written otherwise, as `2..1`, TLC rejects as no set of functions),
  `an empty symmetry function TLC may hold as a tuple or a record`, and `a symmetry of fewer than
  two functions TLC may not enumerate` (TLC counts the arguments of a set it holds as an
  enumeration, and its simulator fails in frames of its own).
- The constant definitions TLC computes as it starts (`processConstantDefns`), besides the
  sections above: `a warning-only startup definition at a limit of the engine's, which nothing
  confirms TLC computes quietly`, `a startup print the engine can't compute, which nothing
  words`, `a definition TLC computes at startup that prints or draws and fails there, named as the
  initial predicate, the next-state relation or the specification` (TLC's report heads its call
  stack with the conjunct that printed, which the evaluator of failures doesn't place), `a
  constant definition TLC computes as it starts with AssertError and effects` (TLCExt's
  AssertError has no minimum level, so TLC computes such a definition once as it starts, with its
  effects, where the engine computes it at each use), `effects or version-specific startup
  inspection before an INSTANCE built-in operator body` (TLC fails with a NullPointerException
  on a definition that reaches an INSTANCE's operator without a body, after what the definitions
  before it showed), and `TLCSet as TLC starts, which fails there` (the constant evaluator's
  reason for a TLCSet of a number or of a key TLC doesn't know, which throws as TLC starts,
  before it has a checker to set).
- TLCExt and TLC builtins, besides the sections above: `TLCEvalDefinition of a name TLC finds no
  definition without parameters of` (`TLCExt.tlcDefByName`), `TLCGet of a simulation's run as
  TLC starts` (before TLC has a simulator), `ToString of TLC's install, where its jar is` (the
  record TLCGet("config") holds names where TLC's jar is installed), `TLCFP of a value TLC
  doesn't fingerprint`, `Warshall of a value that isn't an enumerable set`, `CHOOSE of a value TLC
  doesn't enumerate`, and the replay's `a Json operator's file that TLC fails to read`. The last
  four name failures TLC words, which decline only where the failure's report can't be placed.
- Sets and functions TLC keeps lazy, besides the sections above: `a recursive function TLC keeps
  lazy, of a function constructor`, `IsFiniteSet of a UNION whose sets the engine doesn't hold`
  (`UnionValue.isFinite` asks each set, where the engine can't build the union of an infinite
  one), `generating from a set TLC keeps lazy` (a walk of an action draws from such a set in an
  order the engine doesn't follow), `a lazy value a filter's tuple pattern binds` (a lazy
  function's `toTuple` builds it first), `a lazy filter's membership that fails`
  (`SetPredValue.member`'s message), `a tuple cast of a value that isn't a tuple`, and `a printed
  value whose normalization the evaluator doesn't follow`.
- The front end, besides the sections above: `a substitution for a name TLC's tables may order
  otherwise` (TLC applies the configuration's substitutions in the order of its Hashtable), `a
  class a TLCOverrides index names that isn't beside the spec` and `a TLCOverrides index class
  that isn't a class file` (the index TLC loads its overrides through), `-inv of an expression
  the front end doesn't define` and `-inv of an action or a temporal formula` (TLC checks an
  invariant of its command line as it is, without the configuration's checks of its level), `the
  initial value of the configured SPECIFICATION` (a SPECIFICATION that names a constant, whose
  value TLC prints, of a kind the front end doesn't write), `a command-line module the front end
  can't read` and `a command-line module that declares a CONSTANT, a VARIABLE or an ASSUME TLC
  keeps out of the root module` (a module TLC's command line links beside the root module), and `a property's \A emptiness is not certified for TLC's
  context` (a property's `\A` the front end unrolls over a set it can't show empty in the context
  TLC evaluates it in).
- The command line, besides the sections above: `-postCondition of a name the configuration
  doesn't spell` (TLC reads `-postCondition Module!Def` with its own parser), `-difftrace of a
  value TLC may compare otherwise than its text`, and the DFID trace's `DFID failure trace has a
  value whose printed shape is not retained`, `DFID trace holds a value whose printed shape is not
  retained` and `DFID incomplete action is unknown` (see "Depth-first iterative deepening").
- A recursion without end that overflows TLC's stack, besides "A recursion without end": `an
  assumption that overflows TLC's stack in a spec that prints` and `a recursion that overflows
  TLC's stack in a model that prints or checks more`: TLC reports the `StackOverflowError` as it
  stops, after what printed before it, which the binary shows only where nothing else did.
- The liveness checker (`LiveCheck`), past its search: `a step of the trace its graph lacks`, `an
  empty stack of the search`, `a bad cycle TLC fails to print` (`printErrorTrace` finds no cycle
  from the node), `a behavior graph TLC fails to construct` (`BEGraph.getPath` finds no path), `a
  counterexample longer than its trace`, `a step back into the cycle past the end of the trace`,
  `a step of a counterexample its trace doesn't take`, and `a liveness atom that isn't a boolean`
  (TLC's `Assert.fail` after the atom's evaluation, without a call stack). Each is a shape of the
  behavior graph the checker can't rebuild as TLC prints it.
- TLC's replay of the initial states, which checks each initial state before the one that fails
  again (see "Earlier wrong outputs"): `evaluating the failure again: a check that doesn't hold as
  TLC replays the initial states`, `evaluating the failure again: a check that fails as TLC
  replays the initial states`, `evaluating the failure again: a VIEW that prints as TLC replays
  the initial states` and `evaluating the failure again: a target the constraints exclude or fail
  on`. A check whose definition may be a constant TLC computed as it started, in a replay that
  wasn't told which startup definitions failed: `a check TLC may have computed as it started`.
  One TLC computed as it started whose value isn't TRUE, as the replay of a successor meets it:
  `an invariant TLC computed as it started`, and `a check TLC computed as it started that isn't a
  boolean` where another replay meets one that isn't a boolean.
- The replays of failures, besides those above: `evaluating the failure again: a replay whose
  copies of a filter fail otherwise` (the copies TLC makes of a lazy filter, as its fingerprint
  and its print, fail with another reason than the replay found).

#### Reasons main declines with too, which no section above names

Main declines each of these too, and its fallback list didn't name them. Each declines exactly
the shape it names, as printed after `prove-it: not native yet:` and the prefix of the part that
met it (`<...>` stands for a name or a value the reason prints).

- tlapm (`prove-it tlapm`): shapes of a run whose output depends on the order its decisions come
  back in, on files tlapm can't read, or on a method Prove It doesn't try as tlapm does; see
  "tlapm". `a thread for tlapm's run, which the system refuses`, `tlapm's report of a command line
  without a module`, `the real path of <...>`, `the backtrace tlapm prints as it ends with -I +
  without its standard library`, `a module file tlapm finds but can't read: <...>`, `an empty cache
  directory, which has tlapm write its cache at /`, `a fingerprints file tlapm can't read: <...>`,
  `a fingerprints file tlapm moves aside: <...>`, `toolbox messages of two decisions in flight at
  once, whose order depends on timing`, `a method Prove It can't try as tlapm does: <...>`, `two
  obligations with one fingerprint, where the order decisions come back in decides what one reuses`,
  `CASE errors the SMT encoder numbers in the order decisions come back in`, `Zenon's notes, which
  tlapm copies in the order decisions come back in`, `Isabelle's proofs, which tlapm writes in the
  order decisions come back in`, `results of one fingerprint, of which the fingerprints file keeps
  the one that comes back last`, `an obligation Prove It can't prove as tlapm does: <...>`.
- The command line: a value of an option TLC reads otherwise than the binary
  (`TLC.handleParameters`). `the trace length <...>`, `the aril <...>`, `the worker number <...>`.
- The checker's report of what the engine found: options, traces, simulations and failures whose
  text TLC writes from state the binary doesn't keep, or writes in an order or at a time it doesn't
  follow. `-continue under SYMMETRY or a VIEW`, `-continue with a spec that prints or sets TLC's
  registers`, `a temporal property's counterexample: a lasso the engine doesn't hand over`,
  `-dumpTrace with a POSTCONDITION TLC rejects`, `-dumpTrace into a directory that doesn't exist`,
  `a POSTCONDITION before what TLC prints adding the stopped state`, `-dumpTrace of a trace TLC may
  not find again for a random draw`, `-dumpTrace into the file <...>`, `a state TLC fails to
  fingerprint with an ALIAS or a POSTCONDITION`, `a state TLC fails to fingerprint as it adds it to
  the behavior graphs`, `a state TLC fails to fingerprint as it adds a deadlocked state`, `an action
  the IR lacks`, `an incomplete successor of a model whose actions the IR lacks`, `an incomplete
  successor of a spec that prints`, `an incomplete successor of an action the IR lacks`, `a name the
  IR doesn't carry`, `a record of several fields, which TLC may or may not have sorted`, `a model
  value TLC's order of strings doesn't rank`, `an error trace the trace exploration spec doesn't
  record`, `a lasso back to a state the trace doesn't hold`, `a step back into the cycle the rebuilt
  lasso lacks`, `a module's file the front end can't read, such as a directory or text not in
  UTF-8`, `a configuration error without TLC's code`, `the engine stopped as TLC started`, `a
  configuration in a module's CONFIG section, which TLC reads from a -config ending in .tla`, `-dump
  of states TLC finds as it replays a step`, `an exception without TLC's code`, `an engine invariant
  failed: <...>`, `-dumpTrace of a trace whose successor TLC fails to find again`.
- The engine's compiler and builtins: values the engine doesn't hold as TLC holds them, operations
  TLC fails on whose report the engine leaves to the evaluator of failures (which words them where
  it can), and shapes of expressions the compiler doesn't translate. `IsFiniteSet of a set TLC keeps
  lazy`, `SubSeq of a non-sequence`, `SubSeq outside the sequence's domain`, `a SortSeq comparison
  that isn't a boolean`, `Permutations of a set too large to build`, `IsFiniteSet of a non-set`,
  `BagCardinality of a non-bag`, `expected a bag`, `SubBag of a non-bag`, `SubBag of a bag too large
  to build`, `a Json operator's file that isn't a string`, `JsonSerialize of a value that isn't a
  sequence or a record`, `a membership in SUBSET of a non-set`, `a subset test of a set with
  effects`, `an operator's table applied outside its rows`, `RandomSubset of a count that isn't a
  natural number`, `a Json operator's file the host hasn't read`, `TLCGet of a system property the
  JVM sets`, `TLCGetAndSet of an argument that isn't an operator`, `PickSuccessor on several
  workers`, `TLCCache of an argument`, `an operator argument that takes an operator`, `DOMAIN of a
  non-function`, `modulus by a non-positive number`, `negative exponent`, `zero to the power of
  zero`, `Head of an empty sequence`, `Tail of an empty sequence`, `concatenation of a string and a
  sequence`, `an assertion failed`, `a SelectSeq test that isn't an operator`, `a SelectSeq test
  that doesn't take one argument`, `@@ of non-functions`, `a membership in a union TLC may build or
  order either way`, `a membership in a set operation on an operand with effects`, `a set operation
  TLC reduces on an operand with effects`, `an enumerated infinite set`, `a set TLC reduces that the
  engine holds as no set`, `a JSON key whose text depends on how TLC built it`, `ToString of a value
  whose text depends on how TLC built it`, `TLCModelValue of a value that isn't a string`,
  `streaming a lazy set TLC may have normalized at an earlier use`, `filtered an infinite set`,
  `enumerated UNION of an infinite set`, `enumerated a union with an infinite set`, `a lazy set too
  large to count`, `counted the elements of an infinite set`, `a membership in UNION of an infinite
  set`, `a function TLC keeps lazy applied in another state`, `expansion too deep`, `an unprimed
  variable past the state's`, `a variable past the state's outside ENABLED`, `a definition or an
  argument that reads a register, evaluated more than once`, `an operator used as a value`, `a
  recursive LET definition`, `the operator argument <...>`, `applying a local value`, `applying a
  function definition as an operator`, `a doubly primed expression`, `no CASE arm holds`, `@ outside
  EXCEPT`, `a primed action`, `enumerated a filter of an infinite set`, `a domain TLC keeps lazy
  that reads what may change before it is applied`, `drew from a value that isn't a set`,
  `RandomElement of the empty set`, `a set with too many elements for TLC 1.7.4`, `membership in an
  infinite set by its name alone`, `a function set over a non-set domain`, `a function set of
  non-sets`, `a function set too large to build`, `a lazy set too large to enumerate`, `membership
  in a non-set`, `streaming a lazy set a variable or a bound name holds as TLC built it`, `an action
  quantified over a non-set`, `an action quantified over more bindings than the engine counts`,
  `walking a recursive function of several arguments`, `walking a recursive function over a tuple
  pattern`, `walking a recursive function that assigns`, `walking a recursive higher-order
  operator`, `walking a recursive operator whose argument names variables indirectly`, `a tuple
  pattern in an action's \A`, `an IF condition that isn't a boolean`, `a CASE condition that isn't a
  boolean`, `UNCHANGED in the initial predicate of a variable`, `an assignment the engine can't
  resolve statically at line <...>`, `the left side of => isn't a boolean`, `ENABLED of an action
  that reads TLCGet`, `a value in an instance's scope the IR can't hold`, `a property scope the
  engine can't translate`, `a lazy set of another kind`, `a lazy function that isn't a function
  definition`, `a function definition that isn't one`, `a recursive function that isn't one`.
- The engine's search, simulation and liveness hand-off: states, steps and stops whose report
  depends on what TLC computes as it goes, which the search doesn't follow. `an assumption the
  engine doesn't compile`, `TLC's registers in the liveness checker's atoms`, `a scope the engine
  can't translate`, `a subscript the engine doesn't read`, `a request too short`, `a count that
  isn't a number`, `a lazy set inside a value`, `an integer token`, `an unknown token`, `an unknown
  lazy set`, `no such value`, `a startup definition that fails, which nothing confirms TLC fails
  on`, `a late node where the atoms use TLC's registers`, `an accepting node where the atoms use
  TLC's registers`, `a property violated in an initial state`, `stopped where PROVE_IT_STOP_AT
  asked`, `a constant conjunct of the specification that fails at startup`, `a startup definition
  that failed, in a shared row`, `TLCSet("exit", TRUE) with temporal properties`, `a late node of a
  state whose next states fail, which TLC fails on again`, `a stop the liveness checker doesn't
  follow in a model that prints`, `a stop TLC reports otherwise in a model that prints`, `a stop
  under SYMMETRY or a VIEW in a model that prints`, `a stop where the atoms read TLC's diameter or
  level and something prints`, `a step to a state the search didn't find`, `the caller cancelled the
  simulation`, `a symmetry that isn't a set of functions`, `a diameter the store doesn't hold`, `a
  next-state relation without TLC's actions`, `a step to a state not yet taken`, `a counterexample
  where the atoms use TLC's registers`, `a definition that isn't one`.
- Java overrides (`TLCOverrides` and module overrides beside the spec): class files the front end
  doesn't read; see "Java overrides that stay declined". `a Java class file that ends early`, `a
  Java method descriptor the front end doesn't read`, `a Java class file's constant out of its
  pool`, `a Java class file's modified UTF-8`, `a Java class file's constant the front end doesn't
  read`, `a module override that isn't a class file`, `a Java class file of a version the front end
  doesn't read`, `a Java override class that isn't a plain class`, `a Java override class that
  implements an interface`, `a Java override class TLC may load through a TLCOverrides index`, `a
  Java method descriptor without parameters`.
- SANY's semantic generator, linter and XML exporter: shapes of a module whose report SANY writes
  from its own data structures, which the front end doesn't rebuild. `the stack trace of SANY's
  generator exception`, `an error of SANY's generator that its report doesn't print`, `the stack
  traces of XMLExporter's exception`, `Expected an operator definition`, `Expected a function
  definition`, `Expected a junction`, `Expected a junction with operands`, `Expected a CASE`,
  `Expected an EXCEPT`, `Expected ! in an EXCEPT`, `Expected [ in an EXCEPT`, `Expected a record`,
  `Expected a LET`, `Expected a CHOOSE`, `Expected a label`, `File name '<...>' does not match the
  name '<...>' of the top level module it contains.`, `Could not find module <...>`, `a symbol table
  that pops a module's context`, `Expected a name`, `Expected an expression`, `Expected a LAMBDA`,
  `Expected an operator argument at line <...>, column <...>`, `Expected an operator argument at
  <...>`, `Expected a fact`, `Unexpected proof step`, `a proof's context that is a module's`, `a
  proof without a level`, `A DEFINE step defines no operator`, `an @ step's operator without a
  place`, `SANY's linter following a definition that applies itself`, `a field named like a symbol
  without a location`, `SANY's generator analyzing the modules in another order`, `a reference to a
  node outside a context`, `The definition of <...> has no body`, `the definition of a node outside
  a context`, `a module that is no module`, `An @ refers to an incomplete EXCEPT`, `an instance of
  no module`, `the export of a node that is no expression`, `a context whose HashMap makes a bucket
  a tree`, `a root module that is no module`, `a label that is not a Label node`, `a definition's
  parameter that is not a FormalParam`, `Could not parse module <...> from file <...>` and `Circular
  dependency among .tla files; dependency cycle is: <...>`, where SANY's message heads a report the
  front end doesn't write whole.
- The constant evaluator: values and failures of a constant expression TLC computes as it starts,
  which the front end leaves to TLC where it can't compute them as TLC does. `an integer TLC
  overflows`, `a value that isn't a boolean where TLC wants one`, `a record with a repeated field`,
  `TLC 1.7.4's sets of records`, `a set of records too large to list`, `TLC 1.7.4's streamed sets`,
  `an operator or a function definition as a value`, `a builtin's value`, `a value tested against
  STRING`, `a tuple of bound names`, `an exponent TLC rejects`, `a modulus that isn't positive`, `an
  interval too large to list`, `an operator as a value`, `an operator a scope doesn't bind`, `a
  function definition applied`, `a field of a value that isn't a record`, `a CASE none of whose arms
  holds`.
- SANY's level checking: level errors whose report depends on the order SANY meets them in. `level
  errors of several arguments of an application`, `a bound above action level outside a quantifier`,
  `a logical operator's level error`, `a level error in an infix chain of more than two operands`,
  `a bound without a range`, `level errors of several bounds of a quantifier`, `a NEW symbol without
  a range`, `an assumption without a range`, `a recursive operator whose levels fail to analyze`, `a
  primed argument of a recursive operator that applies another`, `a recursive operator without a
  range`, `primed arguments of both a module's and a LET's recursive operators`.
- The front end: parse, resolution and analysis shapes, and configurations, whose report depends on
  SANY's or TLC's data structures, which the front end doesn't rebuild. `Java classes overriding two
  modules`, `SANY's parse error for module <...>`, `an INSTANCE of a standard module with
  parameters`, `SANY's errors in a BY, USE or HIDE with other errors`, `messages of a module SANY
  doesn't analyze`, `a level check's warnings`, `a module the report doesn't load`, `a recursive
  definition a record's field applies, on which SANY's linter overflows its stack`, `a declaration
  without a range`, `a definition without a range`, `a field named like an instance's definition or
  a fact`, `a field without a range`, `a constant part of a temporal formula that isn't a boolean,
  put in for an instance's declaration`, `temporal properties in TLC 1.7.4`, `a temporal formula the
  tableau declines`, `a model without Init`, `a temporal property TLC rejects after it computes a
  symmetry it may report on`, `a temporal property TLC rejects after it warns about the symmetry,
  with a definition TLC may print as it starts`, `an assumption that passes an operator an argument
  with AssertEq`, `a SYMMETRY the spec doesn't define`, `a SYMMETRY operator with parameters`, `a
  liveness atom that isn't one`, `an error in the specification after a subscript TLC warns of`, `a
  property TLC rejects after it warns of the subscript of [][Next]_v`, `TLC 1.7.4's missing Init`,
  `an error after a constant predicate the engine checks`, `a RECURSIVE declaration of the
  built-in`, `a reference to an operator declared RECURSIVE and left undefined or defined
  otherwise`, `a LET with an INSTANCE and RECURSIVE declarations`, `a LET with RECURSIVE
  declarations within another such LET`, `a LET's RECURSIVE declaration of a name it binds or names
  before it`, `a LET's RECURSIVE declaration that something else binds or defines, or that is
  defined otherwise`, `brackets nested more deeply than SANY's parser can on Java's default stack`,
  `SANY's parse errors`, `a bug of the PlusCal translator`, `TLC 1.7.4's PlusCal errors`, `a file
  extending an inner module that extends another`, `a spec without a file`, `SANY's parse messages
  with a fatal error`, `TLC 1.7.4's parse messages with a fatal error`, `SANY's generator exception
  after a module of the user's`, `a function declared RECURSIVE with operator arguments in a
  recursive section`, `a recursive section after a module, whose declarations SANY may reject`, `a
  module with modules or RECURSIVE declarations in a recursive section`, `an INSTANCE after a module
  in a recursive section`, `a module in a recursive section whose operators aren't defined after
  it`, `a module of the user's that the trace exploration spec uses`, `an error that stops linking`,
  `SANY's generator of TLC 1.7.4`, `SANY's generator exception before the root module`, `TLC 1.7.4's
  semantic errors`, `a labeled ASSUME/PROVE selected other than as a fact`, `a selection within a
  labeled ASSUME/PROVE`, `a labeled ASSUME/PROVE selected as an expression`, `a LET with RECURSIVE
  declarations analyzed again`, `a LET that declares RECURSIVE <...>, a name already bound`, `the
  theorem, step or instance <...> where an operator is required`, `a RECURSIVE declaration without a
  place`, `a module named as a fact that SANY may not find`, `a module named in a DEF clause that
  SANY may not find`, `a DEF clause entry in parentheses`, `a DEF clause entry that is neither a
  name nor an operator symbol`, `an empty USE or HIDE without a place`, `an empty BY without a
  place`, `a module in a recursive section, where SANY's generator throws`, `a unit in a recursive
  section without a range`, `a module-level RECURSIVE declaration of <...>, a name already bound`,
  `a LET function in a temporal formula`, `an operator argument that isn't a definition`, `a
  builtin's value as an argument to a temporal formula`, `a name the configuration substitutes a
  definition for whose value isn't TRUE`, `a constant INIT or NEXT after a definition TLC computes
  with its effects`, `PickSuccessor in a conjunct of the specification`, `a subscript of [][Next]_v
  that an operator leads back to itself, which TLC reads until its stack overflows`, `a
  configuration value TLC doesn't rank`, `differently-typed model values`, `a typed model value
  compared`, `a temporal quantifier over a set TLC fails to list`, `a temporal IF whose condition
  TLC fails to evaluate`, `Proof of a step that does not take a proof`, `a property's \A that TLC
  unrolls`, `an operator's arguments the front end doesn't bind`, `a name in the subscript of
  [][Next]_v that the front end doesn't follow`, `a definition in the subscript of [][Next]_v that
  TLC may compute as it starts`.
- The liveness checker: tableaux and behavior graphs it doesn't build as TLC's `LiveCheck` does. `an
  action without a step`, `a temporal formula in a single step`, `a liveness trace TLC couldn't
  re-create`, `a step the search didn't take`, `a liveness counterexample TLC failed to build`, `an
  empty trace`, `a late node of a state the engine didn't expand`, `a formula cut short`, `a formula
  with terms past its end`, `a formula that ends early`, `a term that isn't an atom`, `a graph
  without its steps`, `a temporal formula too large in disjunctive normal form`, `an action in the
  tableau`, `a junction of one term in the tableau`, `a temporal formula with actions not of the
  forms <>[]A or []<>A`.
- `-coverage`: costs and counts the port of TLC's cost model doesn't compute as TLC does. `a search
  the pass stopped early`, `a node of a standard module`, `a constant replaced by a definition whose
  body is no application`, `a definition the IR doesn't hold as one`, `an operator that takes an
  operator`, `a LOCAL function definition`, `an operator's parameter applied to arguments`, `a name
  bound outside the expression, as by an INSTANCE`, `a variable of ENABLED's rewrite`, `a recursive
  function applied as an operator`, `a RECURSIVE operator the configuration substitutes`, `a name
  the IR doesn't resolve`, `a built-in operator used as a value`, `a built-in operator of another
  arity`, `an operator applied to another number of arguments`, `a CASE arm without a place in the
  source`, `a record field without a place in the source`, `an EXCEPT without a place in the
  source`, `an EXCEPT of a function of several arguments`, `an integer outside 32 bits`, `a real
  number`, `an operator passed as an argument`, `a recursive function construction`, `a bracket
  expression`, `a definition as an expression`, `an infix junction of fewer than two operands`, `an
  infix junction without the places of its prefixes`, `a definition without a place in the source`,
  `a module whose source the port can't read`, `a definition outside its module's source`, `a
  definition whose name the port can't place`, `a definition whose parameters span lines`, `a
  variable whose declaration the port can't place`, `a CASE arm SANY may place apart from its
  expressions`, `an OTHER arm the port can't place`, `a record field the port can't place`, `an
  EXCEPT the port can't place`, `a VARIABLE declaration the port can't place`, `a module with
  modules inside it`, `a function TLC keeps lazy inside another value`, `a non-boolean where TLC
  expects a boolean`, `a constant definition whose value TLC computes at startup fails`, `a variable
  TLC reads unassigned`, `a prime TLC evaluates in no next state`, `an action TLC evaluates in no
  next state`, `a tuple bound to a value that isn't one`, `a UNION TLC keeps lazy (UnionValue)`,
  `DOMAIN of a value TLC can't take it of`, `a set operation TLC keeps lazy of a set with a cost
  model`, `a union TLC keeps lazy (SetCupValue)`, `a lazy function of several parameters applied`,
  `a function of several parameters TLC builds`, `an EXCEPT of a key the function lacks, which TLC
  warns of`, `a set TLC streams in an order of its own`, `an enumeration of a value that isn't a
  set`, `an enumeration of a lazy set the port doesn't follow`, `a set enumeration of a value that
  isn't a set`, `an equality of a lazy set with a cost model`, `a membership of a lazy function with
  a cost model`, `an initial predicate that isn't a boolean expression`, `a LET where TLC looks for
  a variable`, `a next-state relation that isn't a boolean expression`, `a lazy function applied in
  the next-state relation's walk`, `a variable changed that the action leaves UNCHANGED, which TLC
  warns of`, `an EXCEPT of a value that isn't a function`, `an initial predicate that isn't a
  definition`, `an action TLC names by an operator that isn't a definition`, `a state TLC finds
  incomplete`, `a state that holds a set TLC keeps lazy`, `a state the port can't fingerprint as TLC
  does`, `an initial state TLC finds incomplete`, `a successor TLC finds incomplete`, `a value whose
  fingerprint the port doesn't compute`, `an initial state TLC doesn't find again`, `a successor TLC
  doesn't find again`, `a lookup of the cost model TLC fails, at <...>`.
- The evaluator of failures and traces: failures, replays, trace rebuilds, dumps and postconditions
  whose report TLC writes from values or order the evaluator doesn't keep. `that uses registers the
  rebuild of the trace sets`, `record with a key that isn't a string`, `a dumped trace <...>`, `of a
  value too large to write`, `of a model value the configuration doesn't make`, `of a record with a
  field that isn't a name`, `of a set or function TLC keeps lazy`, `of a set or function TLC can't
  write as JSON`, `a function's value the walk tests that isn't a boolean`, `an assumption after the
  configuration's predicates or a symmetry`, `an assumption the model doesn't have`, `an assumption
  that isn't a boolean`, `an assumption that sets a register`, `an assumption that is no boolean,
  without a range`, `evaluating the failure again: a state TLC fails to fingerprint before an atom
  fails`, `evaluating the failure again: an atom that fails after a failure that prints`,
  `evaluating the failure again: an invariant of an initial state`, `evaluating the failure again:
  an atom without a state`, `evaluating the failure again: the initial state TLC's replay fails at`,
  `evaluating the failure again: an initial state's check past the initial states`, `evaluating the
  failure again: Next's and an atom's at once`, `evaluating the failure again: an implied init in an
  instance's scope`, `evaluating the failure again: an implied init the model doesn't have`,
  `evaluating the failure again: a check the model doesn't define`, `an atom the model doesn't
  have`, `evaluating the failure again: an earlier invariant is violated`, `evaluating the failure
  again: an initial state the path lacks`, `evaluating the failure again: an initial state the
  replay didn't find`, `replaying the expansion under a VIEW or SYMMETRY`, `replaying the expansion
  without the fingerprints the search found`, `evaluating the failure again: TLC's replay of the
  initial states doesn't fail`, `evaluating the failure again: TLC's replay of the initial states
  prints or fingerprints`, `no state to expand`, `the next-state relation doesn't split`, `the next
  states fail`, `a successor whose fingerprint the evaluator can't tell`, `an invariant's scope`,
  `the step to the successor that failed holds`, `a successor outside the model that violates an
  invariant`, `no step to the successor that failed`, `an incomplete successor of no state`, `a
  successor of a model without a next-state relation`, `no successor is incomplete`, `an invariant
  the model doesn't define`, `an earlier invariant is violated`, `a constraint the model doesn't
  define`, `reading a count past an int`, `the IR doesn't define`, `of a model whose ALIAS fails`,
  `of a step whose action the trace lacks`, `of an action without a location`, `dumped with an
  action's parameter TLC may share`, `of a lasso outside its trace`, `of an action of an operator a
  LET defines`, `of an action of a function definition`, `a definition of a numeral TLC can't hold`,
  `a VIEW without a definition`, `an atom the checker asks nothing of`, `the second rebuild of a
  trace of a spec that draws at random`, `a state of another width than the model's`, `a trace whose
  initial state TLC fails to rebuild from the generator it resets`, `no initial state is the trace's
  first`, `a trace of a model without a next-state relation`, `an action the model doesn't have`, `a
  successor whose checks no longer fail`, `a constraint without a definition`, `an invariant without
  a definition`, `TLC's actions of a model whose startup fails: <...>`, `TLCGet("spec") of a model
  whose startup fails: <...>`, `an action's parameters of no operator`, `TLC's actions of a model
  without a next-state relation`, `TLC's actions of a next-state relation in a scope: <...>`, `a
  next-state relation TLC fails on as it starts, an action of which is a literal`, `TLC's actions
  through an operator bound locally`, `TLC's actions through a LET: <...>`, `TLC's actions whose
  split prints, draws or sets a register`, `an action's parameter TLC keeps as a lazy set`, `a value
  the search left holding a function TLC keeps lazy`, `a membership in the union of a set TLC
  doesn't enumerate`, `an effect under an assignment from a set TLC streams`, `an assignment from a
  set TLC streams`, `an order of strings TLC made as it searched`, `an ALIAS TLC rejects`, `a set
  that isn't one`, `ToString of a lazy set`, `a literal walked as an action, as TLC prints it`, `a
  field that isn't a string`, `a startup definition that failed there and not where it is used`,
  `BagUnion of a set whose element isn't a function`, `a function of several bounds or a tuple
  pattern TLC keeps lazy`, `a lazy function TLC prints with effects or a report of its own`, `a
  filter TLC keeps lazy whose predicate has effects`, `TLCGet("spec") the IR doesn't hold`,
  `Cardinality of a value TLC doesn't enumerate`, `SubSeq of a bound that isn't an integer`,
  `ToTrace of a state that isn't numbered`, `ToString of a record TLC may have sorted`, `a sub-bag
  that isn't a function`, `SubBag of a bag with a count that isn't positive`, `TLCModelValue of a
  name TLC ranks as it runs`, `a value of TLCGetOrDefault a failure may name the source of`, `TLCFP
  of a value the evaluator doesn't fingerprint`, `Permutations of a value that isn't a set`, `a
  union with a later set TLC doesn't enumerate`, `a bag's count that isn't an integer`, `a subscript
  the replay doesn't read`, `an action TLC evaluates of an initial state`, `a constraint that prints
  as TLC replays the initial states`, `a constraint that fails as TLC replays the initial states`,
  `a state TLC fingerprints only where its constraints hold`, `a state TLC fails to fingerprint and
  print`, `a constraint that isn't a boolean`, `a constraint that isn't a boolean, without a range`.
- The value store: values TLC fingerprints, prints, converts or compares by their Java class, which
  the store doesn't keep. `fingerprinting a function TLC keeps lazy, or Nat, Int or STRING`, `a
  function key the store didn't intern`, `JSON of a function TLC keeps lazy, or Nat, Int or STRING`,
  `a JSON string the engine made unranked`, `a key whose letters Unicode's categories decide`,
  `printing a function TLC keeps lazy, as TLC writes it`, `a function over an interval compared with
  one over other keys`, `a record compared with a function of its size over a model value`,
  `membership of a value TLC can't compare`, `handing over a function TLC keeps lazy, or Nat, Int or
  STRING`, `a part not read before`, `an unknown tag`.

#### Declines to win back where main matches

Probes of past specs outside the corpus (11,715 runs at one and four workers) found 93 runs main
answers as TLC that declined here. 88 of them answer now (the 11 and 76 below and the one
last below) and 5 still decline. The probes of a substitution's target Y below each surround Y's
computation with readers: `CONSTANT K <- A`, `L <- A` and `A = [Probe] 9` (or `{9}`) in the
configuration, `A == 1+1` (or `{2}`), and `Before`, `Middle` and `After`, each the same reader of
A, defined before K, between K and L, and after L, read by an assumption such as
`ASSUME PrintT(<<Before, Middle, After, A>>)` or `ASSUME Ignore(Before)` with
`Ignore(x) == TRUE`. The reasons were:

- `a constant definition TLC computes as it starts that sets a register` (11 runs), as `Test ==
  PrintT({y \in {x \in 1 : FALSE} : TLCSet(0, 3)})` or `Cardinality({y \in {x \in STRING :
  TLCSet(0, 3)} : 1}) = 0` in an assumption, where TLC fails on the inner filter's base
  (`Attempted to enumerate { x \in S : p(x) } when S: 1 is not enumerable`) before it reaches
  TLCSet. These answer now: TLC builds `{x \in S : p}` of an S it can't reduce lazily
  (`OPCODE_sso`), and enumerating it fails before p where S, or the base of such a filter, is a
  number, a string, a boolean, `STRING`, `Nat` or `Int`, or a tuple, a record, a function or
  `Seq(T)` built without effect (`SetPredValue.Enumerator`); a set map, a quantifier, CHOOSE, an
  equality's left side, `Cardinality` and `PrintT` (also of a tuple whose other elements have no
  effect) enumerate it first, so the definition fails as TLC starts before any effect
  (`fails_first_at_startup`). A base built with an effect that TLC fails on first answers too:
  `PrintT({x \in [i \in 1..2 |-> TLCSet(0, i)] : TRUE})` (`tlcset-function-built-at-startup`),
  as TLC builds a function constructor over set enumerations and intervals that aren't empty
  at once where no application keeps it lazy (OPCODE_fc's `toFcnRcd`), the body first at the
  domain's first element, where its TLCSet of a number fails as TLC starts. So does one whose
  key is the constructor's one bound name over an interval or a set enumeration of numbers, and
  whose value has no effect, as `[i \in 0..2 |-> TLCSet(i, i)]`: its key at the first element is
  a number too. A key that is any other expression of the bound name (`TLCSet(i + 1, i)`), or a
  name over another set, still declines.
- `a substitution whose target has a module-scoped value the spec reads otherwise` (81 runs),
  where a substitution's target Y also has a module-scoped configuration value. The shapes where
  which value a read finds doesn't show answer now (see "Scoped configuration entries"): two
  substitutions with readers of Y nothing reads (`ASSUME Ignore(Before)`, `ASSUME TRUE` beside
  `Before`, `Middle` and `After`, or one of them printed beside others nothing reads), an entry
  with arguments for a Y without parameters whose body isn't a literal (`C <- A`, `A == 1 + 1`,
  `A(0) = [Probe] 7`, `ASSUME PrintT(A)`), a Y whose body the constant evaluator doesn't compute
  but TLC certainly computes without effects as it starts (`certainly_computes`, now also a
  function over a certainly empty domain), early readers that all fail reading the entry, a
  table on a literal body nothing reads, and a target of a scoped substitution where the entry
  is left out. Of the 81, 76 answer now and 5 still decline. Those that answer since the 43
  include 22 whose Y's draws decide only whether computing it fails (`A == IF
  RandomElement({TRUE, FALSE}) THEN 1 ELSE 1 \div 0`, and such an IF whose other branch prints or
  draws after or before, at one and at four workers: see "Scoped configuration entries"), two
  whose Before TLC builds lazily over `SUBSET {1}` (a function whose body, and a filter whose
  predicate, reads A), one whose Before TLC fails to build at once over `{9}` (`[v \in {A} |-> 1
  \div 0]`, read by `ASSUME DOMAIN Before = {A} /\ DOMAIN After = {A}`), and two that never
  evaluate C (C unread, or named only by a LET definition the LET's body doesn't use). The 11
  that declined (the last 6 answer now):
  - 3 (`A == RandomElement({1,2,3})`, read through K before L, through L before K, and in a
    set TLC normalizes) where Y's draws decide its value. Main
    matched by chance of the seed: the harness runs TLC at `-seed 4`, and the same specs with
    only the seed changed (`-seed 0` to `7`) print `<<1, 1, 2, 1, 2, 1, 1>>`, `<<2, 2, 1, 2, 1,
    2, 2>>`, `<<3, 3, 2, 3, 3, 3, 3>>`, ... on TLC for `PrintT(<<Before,A,K,A,L,A,After>>)` and
    `2`, `1`, `2`, `1` for the set at `-seed 0`, where main prints `<<3, 3, 3, 3, 3, 3,
    3>>` and `3` four times at every seed: TLC computes A again at K and at L and draws again at
    each read of K or L. It matches only at `-seed 4`.
  - 1 (an ELSE that prints `"before"` and then fails, at `-seed 4`). Main matched by chance of the seed: at `-seed 0`, `1`, `3`, `5`, `10`, `11` and
    `12` TLC prints `"before"` and then `1`, as its computation of A at K or at L takes the ELSE,
    where main prints only `1`; it matches where both draws take the THEN.
  - 1 (`Before == {v \in SUBSET A : A = {9}}` with
    `A == {2}`, `A = [Probe] {9}`). Main matched by chance of the predicate: TLC computes the
    base `SUBSET A` as it builds Before, reading the entry, and the predicate, false either way,
    hides it. With the predicate `A = {2}` TLC prints `<<{{}, {9}}, {{}, {2}}, {{}, {2}},
    {2}>>` and main `<<{{}, {2}}, {{}, {2}}, {{}, {2}}, {2}>>`.
  - 6 (`C <- A`, `A == 2`, `A(0) = [Probe] 7`, and `ASSUME C`, `DOMAIN [v |-> C] =
    {"v"}`, `Tail(<<C>>) = <<>>`, `<<1,C>> = <<2,C>>`, `Len(<<C>>) = 1`, `<<C>> = <<>>`). These
    were not matches by chance: TLC's C is the table `{ <0, 7>}` through the literal body, but
    none of them looks into it, and `ASSUME C` fails as `TLC expected a boolean value` for any
    number or string body (`A == "s"` too). They answer now, as main does, where every read of
    C is one TLC never looks into (see "Scoped configuration entries"); a read that shows it
    (`PrintT(C)`, `C = 2`, `LET D == C IN D = 2`) prints `{ <0, 7>}` or fails comparing it on
    TLC, where main prints 2 or holds, and still declines.
- `a configuration substitute with effects, which TLC computes again where it reaches the
  definition it replaces` and the decline above, of neighbours of these probes where a
  substitution's target draws (see "Scoped configuration entries"). Main matched those by chance
  of the seed: with `A == IF RandomElement({TRUE,FALSE}) THEN 1 ELSE 1 \div 0`, `K <- A`, `L <-
  A` (with or without `A = [Probe] 9`) and `ASSUME PrintT(<<K, A, L>>)`, main prints `<<1, 1,
  1>>` at every seed, where TLC, drawing again at each read of K and L, fails on `\div` at `-seed
  1`, `2`, `3`, `5`, `6` and `7` with the entry and `1`, `3`, `4`, `5` and `6` without it; with
  `A == IF RandomElement({TRUE,FALSE}) THEN 1 ELSE 2` and `ASSUME PrintT(A)`, main prints 2 at
  `-seed 2718281828` where TLC, keeping L's draw, prints 1. Main matches, not by chance, where
  the target's value can't vary with what it draws and nothing draws after it, with `K <- A`,
  `L <- A` and `ASSUME PrintT(A)`: `A == IF RandomElement({1}) = 1 THEN 1 ELSE 2` and `A == IF
  RandomElement(1..65) = RandomElement(1..65) THEN 1 ELSE 1` in all five contexts, and `A == IF
  RandomSubset(1, {1, 2}) = {3} THEN 1 \div 0 ELSE 1` as an assumption. These still decline, as
  declines to win back.
- Readers of Y on both sides of where TLC computes Y, both read, or one read with effects
  (`Before == A` and `Middle == A` read by `PrintT(<<Before, Middle>>)`, or `Before == PrintT(A)`
  beside `PrintT(Middle)`), none in the 81. Main reads Y's body everywhere, so it prints Before
  as 2 where TLC prints 9 (`<<9, 2, 2>>` for `<<Before, Middle, After>>` on TLC, `<<2, 2, 2>>`
  on main) and matches only where the value Before read doesn't show, by chance. Winning them
  takes keeping, for each definition TLC computes before Y, the value it computed reading the
  entry, while Y reads its body.
- `a scoped override whose target has a module-scoped override` and `a definition the
  configuration names whose body a module-scoped substitution replaces` (17 runs of later
  probes): `J <- [Base] K` beside `K <- [Probe] B` with `K == TRUE` (5), and a CONSTRAINT or
  ACTION_CONSTRAINT `P` beside `P <- [M] Q` that the next-state relation also reads (12), answer
  now (see "Scoped configuration entries"). Of their neighbours, a literal K (`K == 3`, where TLC
  fails with the cast of an `OpDefNode` to a `Value` and main prints 3) and an INVARIANT P that
  the next-state relation reads (where TLC reads Q for the reference and main P's body) still
  decline; main matched those only where the two values agree. The chained shapes with a T or
  an S that reads variables or has effects (10 runs) answer now too; one above state level still declines, as above.
- `a constant definition TLC computes as it starts that sets a register`, of `TLCSet(k, v)`
  whose key fails as TLC builds it but in a way the front end's evaluator doesn't compute, as
  `TLCSet(<<1, 2>>[3], PrintT(1))` (5 contexts) or `TLCSet([i \in {1} |-> 1 \div 0], PrintT(1))`
  (assume, init, next), where v has an effect. TLC evaluates the key first, and where it fails
  there the print never runs and main, which computes the definition only where it is read,
  shows the same. Main matched these by chance: where the key builds and TLC rejects it, as
  `TLCSet(<<1>>, PrintT(1))`, TLC prints 1 as it starts and again at the use, and main prints it
  once (wrong in the assume context; the others decline on main), and main is wrong too on
  `TLCSet(<<PrintT(0), 1 \div 0>>, PrintT(1))` and `PrintT(0) /\ TLCSet(<<1 \div 0>>, PrintT(1))`
  in all five contexts and on `TLCSet(Nat, TLCSet(1, PrintT(2)))` as an assumption. These answer
  now where the engine, computing the definition as TLC starts, finds the key failing before any
  effect (`tla_ir::Startup::register_probes`), and the neighbours main is wrong on still decline,
  as the probe meets their print first.
- `a substitute whose recursion may overflow TLC's stack as it starts`, of a `CONSTANT C <- D`
  whose recursion ends after more than 50 nested calls but before TLC's stack overflows, as `D ==
  S(600)` or `D == F[600]` of the one-operator shapes above (where TLC evaluates up to about
  900 and 750), or a recursion that fails on `1 \div 0` after 101 calls, which TLC swallows.
  Main matched these by chance of the body: the same `S(150)` overflows TLC's stack where S
  reaches the next call through 8 operators, and main prints a clean run there (see the
  substitute paragraph above).
- `a constant definition TLC computes as it starts that sets a register`, of a definition whose
  only TLCSet is of "exit" or "pause" and a literal other than TRUE beside a print, as `Test ==
  PrintT("before") /\ TLCSet("exit", FALSE)` or `TLCSet("pause", FALSE) /\ PrintT("after")` (35
  runs of such shapes in the assume, init, next, invariant and property contexts). TLC computes it
  once as it starts, prints there, and keeps its value; the front end counts TLCSet state-level,
  so the engine would compute it at each use. Main matched these by chance, where the one read
  came once: with `ASSUME Test` twice it prints twice, with the definition unread it prints
  nothing, under an invariant over three states it prints three times, and `TLCSet("pause", 1)
  /\ PrintT("after")` in Next prints at each step, where TLC prints once in each. Counting such a
  TLCSet constant-level, as TLC's level of the Java method is, wins them.
- One run (`A == Any` and `SUBSET A = SUBSET A` in an
  assumption) declined with `an assumption that fails to evaluate: evaluating the assumption
  again: a failure ...`; it now matches TLC.
- A second corpus of past specs (17,340 runs at one and four workers) found 50 runs main
  answers as TLC that declined here. 12 answer now: eight startup definitions with a draw the
  engine doesn't compile, in an assumption (`unsupported: RandomSubset`, "Print where TLC
  evaluates it otherwise", "a value TLC computed at startup with effects"; see the paragraph on
  startup definitions that draw), three LET functions TLC keeps lazy and prints a copy of, or
  applies before (see "Functions TLC keeps lazy"), and an ALIAS rebuilding one. Of the 38 that
  still decline, main matched eight by chance: five where TLC's workers print in an order a race
  decides (`prints TLC's workers may make in any order`: `Next == x' \in {1, 2} /\ PrintT(x')`
  at four workers, which in 20 more runs of the jar printed each of four or five orders of its
  six prints, as `1 2 1 2 1 2`, `1 1 2 2 1 2` and `1 2 1 1 2 2`, with a depth of 2 or 3), two
  stops several workers race to (`a stop several workers race to`: in 20 more runs the jar
  showed a trace from `x = 0` 13 times and from `x = 1` 7 times for an invariant two initial
  states reach, and through `x = 1` 16 times and `x = 2` 4 times for a division by zero two
  successors reach), and `<<R, RandomElement({1, 2})>>` (above). Eight read how long TLC ran in a
  POSTCONDITION: three answer now (two reads of `TLCGet("stats")` compared, a `>=` the spec
  defines and a LET function's DOMAIN; see the postcondition paragraph above), and of the others
  `FALSE \/ d = 7`, `d >= 0 /\ d = 99` and `TLCGet(d \div 1000000) = 1` main matched by chance,
  as the jar shows there. Three are substitutions and two set a register as TLC starts, under the
  reasons above. 17 were to win back, and 14 answer now: an
  INSTANCE fact literal TLC did not initialize (five contexts of one spec), a membership in the
  domain of a function TLC keeps lazy (four), a function TLC keeps lazy in an argument, applied
  (two, as `PrintT(g) /\ g[{}] = 1`), AssertError with effects (one), a function over a set TLC
  fails to sort (one) and the copy of an inner module with parameters whose definition draws as
  TLC starts (`I!IR` above), each as the paragraphs above say. Three still decline: a LET
  INSTANCE of a module without parameters four of whose definitions draw `RandomSubset(0, 1..9)`
  as TLC starts, which main matches at every seed only because a draw of no element is `{}`
  whatever the generator holds (a decline to win back), and IOUtils's Serialize in a definition
  nothing reads (two), which main matches only in the transcript: the Jar writes the file as it
  starts and main writes nothing (see "IOUtils's Serialize" above), so they stay declined.
- A later pass took the 33 runs outside the corpus main matched that still declined without
  evidence of chance, and 24 answer now: seven substitutions whose reader of Y TLC computes
  before Y holds it lazily or fails (`Before \cup {}`, `{Before}`, `DOMAIN Before`, `LET L ==
  Before IN L`, an unread `Before \subseteq {}`, a filter over `[{1} -> {1, 2}]`, and `Before ==
  Assert(A # 9, "boom")`); `A == IF RandomElement({1, 2, 3}) = 1 THEN 1 ELSE 1 \div 0` and its
  CASE form at the two seeds of 12 main answers (it declines at the other 10, as main does); and
  13 register probes in the init, next, invariant and property contexts and as assumptions
  (`(RandomElement(SUBSET {1, 2}) = {3}) /\ TLCSet(1, 2)`, `(RandomSubset(1, {0, 2}) = {1}) /\
  TLCSet(1, 2)`, `D == RandomElement({0, 2})` with `(D = 1) /\ TLCSet(1, 2)`), as the paragraphs
  above say (`scoped-target-early-reader-held-*`, `-tested-subset`, `-function-set` and
  `-assert-fails`, `scoped-target-draw-boolean-condition`, `tlcset-after-subset-draw`,
  `tlcset-after-random-subset` and `tlcset-probe-reads-earlier-draw`). Nine still decline:
  - `Test == (PrintT("a") /\ RandomElement({0, 2}) = 1) /\ TLCSet(1, 2)` in the init,
    invariant and property contexts (3). TLC computes Test once as it starts, printing `"a"`,
    and keeps FALSE; the engine, counting TLCSet state-level, computes it at each use. Main
    matches only because each of these contexts reads Test once: with `Init == s = (Test \/
    Test)`, or an invariant `~Test` over two initial states, main prints `"a"` twice where TLC
    prints it once (wrong on main, declined here). Winning them takes the engine keeping a
    register probe's value where it completes without reaching TLCSet, which neither the
    search nor the trace evaluator does for a definition counted state-level.
  - Four assumptions whose probe meets an effect beside another startup definition, or one the
    engine doesn't compile in a probe: `D == (RandomElement({0, 2}) = 1) /\ TLCSet(1, 2)` with
    `Test == PrintT(<<D, RandomElement(1..1000)>>)` (the engine computes Test, drawing D's draw
    inside it, before it probes D, whose draw then moves the generator), `Test == D \/
    PrintT(<<D, D>>)` (two probes, the second printing reads of the first: "Print where TLC
    evaluates it otherwise"), `D == RandomElement({0, 2})` with `Test == ((D = 1) /\ TLCSet(1,
    2)) \/ PrintT(<<D, RandomElement(1..1000)>>)` and `(RandomElement({x \in 1..3 : PrintT(x)})
    = 5) /\ TLCSet(1, 2)` (a draw in a print's argument and a print in a filter's predicate,
    which the engine compiles in a probe nowhere).
  - `([k \in {1, 2} |-> k] = (<<1>> @@ <<RandomElement({0, 2})>>)) => TLCSet(1, Print("p2", 2) +
    RandomElement({0, 1}))` as an assumption: the engine doesn't compile a draw in `@@`'s operand
    in a probe, and the front end's evaluator, which holds no functions, can't show that the
    implication's left side is FALSE for every draw.
  - The LET INSTANCE of a module whose definitions draw `RandomSubset(0, 1..9)` as TLC starts,
    at four workers (above): main matches at every seed only because a draw of no element is
    `{}` whatever the generator holds; the front end declines every INSTANCE copy that TLC
    computes as it starts with effects.
- `a constant definition TLC keeps as a lazy set whose effects it has as it first converts it`,
  of a set enumeration whose element is a definition that reads a register and that the engine
  doesn't compute as TLC starts: `D == PrintT("d") /\ TLCGet(1) = 1` after `ASSUME TLCSet(1,
  1)`, read by `S == {D}` with `Test == Cardinality(S) = 1 /\ Cardinality(S) = 1`, or `D ==
  PrintT(<<"d", TLCGet(1)>>) /\ TLCGet(1) = 1` with `Test == D /\ S = {TRUE}`, in the init, next,
  invariant and property contexts (8 runs; as an assumption they answer). Main matches these,
  not by chance: they are declines to win back (see the paragraph on constant definitions held
  as a lazy set). Winning them takes the engine telling whether TLC kept S's value as it started
  or computes it again at each use. Set enumerations whose element is a LET's name or an
  operator's application, which declined with the same reason where main matched, answer now.
- `what the spec prints as TLC computes its constants`, of a register probe whose TLCSet fails
  before anything it prints, before a configuration error (`D == TLCSet(1, 2) /\ PrintT(8)` or
  `Print(8, TLCSet(1, 2))`, with no INIT or with `CONSTRAINT Nope`): main matches these only by
  chance. It never prints what a register probe prints as TLC starts before such an error, and
  is wrong wherever the print comes first (`PrintT(8) /\ TLCSet(1, 2)` with no INIT, or with an
  INVARIANT, PROPERTY, CONSTRAINT, ACTION_CONSTRAINT, VIEW or SYMMETRY that isn't defined, and
  the other shapes of the paragraph on printing constant definitions above). Winning them takes
  the front end telling, in TLC's order, whether TLCSet comes before every print.

- Prints of a function, a tuple or a set whose values are set enumerations, maps or unions of
  numbers, where the engine can't tell how TLC built the value it prints and so declines
  ("printing a value whose text depends on how TLC built it"): an EXCEPT of such a function
  (`PrintT([[x \in {1,2} |-> {x}] EXCEPT ![1] = 0])`, also of a LET name or of an INSTANCE
  substitute), an operator's parameter bound to one (`Op(S) == PrintT(S)` or `PrintT([S EXCEPT
  ![1] = 0])` with `Op([x \in {1,2} |-> {x}])`), a LET function also applied (`LET g == [x \in
  1..2 |-> {x, 0}] IN g[1] = g[1] /\ PrintT(g)`, `{3} \cup {x}`, `LET f == [y \in 1..2 |-> {y}]
  IN PrintT(f) /\ PrintT(f[2])`, `PrintT(f) /\ f[1] = {1,3}`, a recursive `LET f[y \in 1..2] ==
  ...`), and values reached through a record field, a tuple index, CHOOSE or a LET name inside
  the function's body (`PrintT([y \in 1..2 |-> [a |-> {3,y}].a])`, `<<{3,y}>>[1]`, `CHOOSE s
  \in {{3} \cup {y}} : TRUE`, `LET s == {3} \cup {y} IN <<s, s>>`, `(y..y) \cup (3..4)`), in all
  five contexts (245 probe runs). Main matches these, not by chance: OPCODE_se and
  `SetEnumValue.cup` always build a set enumeration, never an interval, `SetEnumValue.toString`
  normalizes, and `FcnLambdaValue.toString` prints `toFcnRcd()`, so the text can't depend on how
  TLC built a set of numbers there. The engine follows how a printed value is built only through
  the expression written (`Construction`), which an EXCEPT, a parameter or a kept LET function
  leaves unknown, and a singleton or consecutive set of numbers it holds may be an interval
  another expression built. Winning them takes following the construction through EXCEPT,
  parameters and kept LET functions, or proving that nothing the printed value is built from
  makes an interval or a record of several fields.
- Substitution tables on a literal body read only where TLC never looks into the table, beyond
  the shapes `get_uninspected_parts` follows (14 probe runs, listed in "Scoped configuration
  entries"): main matches them, not by chance, since none of them looks into C. Winning them
  takes extending `get_uninspected_parts` to elements nested in another constructor under Len,
  to the components Head, application and field access read, and to a first differing element of
  any kind and position.
- Uses of an INSTANCE fact literal TLC did not initialize (`{N!A}`) other than the enumeration of
  a set holding it (listed under the null tool values), as `DOMAIN [v \in {N!A} |-> 1] = {}`,
  `({N!A} \cup {}) = {}` and `Len(SelectSeq(<<N!A>>, LAMBDA x : TRUE)) = 1` in all five contexts
  ("a null tool value used by a consumer the replay does not model", "an equality involving a
  nested null tool value", "an INSTANCE fact literal TLC did not initialize"). Main matches
  these whatever the instance's parameter is; `{N!A} \subseteq {1}` main matches only because
  the parameter is 1 (by chance). Winning them takes modelling TLC's null value in each consumer.
- Action splitting through an \E over the empty set whose body holds a name TLC would cast,
  `Next == x' = x \/ \E i \in {} : x` and `Next == \E i \in {} : x \/ x' = x` with `Init == x =
  FALSE`, decline ("a variable, a constant or a parameter TLC's splitting of the next-state
  relation fails to cast to a definition inside an operator's application, a LET's definition or
  an \E, ..."), where main matches, not by chance: `getActions` splits an \E at each binding
  of its bounds, and over an empty domain (`Enum.isDone()`) it takes the \E whole as one action
  without walking its body, so nothing is cast, and that action adds no step. Winning them takes
  deciding, before the cast test, that the \E's bounds are certainly empty.
- A function constructor whose first bound is a set enumeration of an uninitialized INSTANCE
  fact literal and whose later bound fails, `[v \in {N!A}, w \in {1 \div 0} |-> 1] = <<>>`, in the
  initial predicate, the next-state relation, an invariant and a property, at one and four workers
  ("the engine stopped: an INSTANCE fact literal TLC did not initialize"). Main reports the
  division by zero as TLC does, but by chance: it reads `{N!A}` as a set of one value, so it is
  wrong where the null bound decides the result, as `\E v \in {N!A}, w \in {1} : TRUE`, `\E v
  \in {N!A} : TRUE` and `\E v, w \in {N!A} : TRUE` (false in TLC, true on main) and `\A v \in
  {N!A}, w \in {1} : FALSE` (true in TLC, false on main), in all five contexts. Here the later
  bound's failure comes first either way. Winning them takes compiling a function constructor's
  bound over such a set the way the engine compiles a quantifier's, holding the null in the
  domain TLC keeps.
- `Next == C(RandomElement({1, 2}))` with `C <- Op`, where the spec draws elsewhere and the draw
  shows (see "A literal as an action"): main matched those by chance, as listed there.
- An EXCEPT of a lazy function past its first key, `LET g == [i \in {1,2} |-> i] IN [g EXCEPT
  ![1].a = 0][1]` ("an EXCEPT of a lazy function past its first key ... evaluating the failure
  again"), in all five contexts: TLC fails applying the inner EXCEPT to g's value 1 at the key
  ("Attempted to apply EXCEPT construct to the value 1."), and main reports that failure as TLC
  does, not by chance. Winning it takes following the EXCEPT's update path into the lazy
  function's value at the key where the evaluator now stops.
- A Json or IOUtils operator that writes to what isn't a regular file, a pipe or a device, as
  `ASSUME JsonSerialize("/dev/stdout", <<123>>)` ("JsonSerialize, whose file the replay doesn't
  read or write"). TLC writes `[123]` into its own output and completes, and main does the same,
  not by chance. Here a run holds its output until it knows it won't decline and keeps each file
  as it was before it writes it; a pipe has no bytes to keep and a read of one may never end, and
  bytes written past the hold would come before what the run holds. Winning it takes writing such
  a destination through the hold where it is the run's own output, and for another only once the
  run can no longer decline.

#### Every reason

This is a historical measurement with `bun scripts/run.ts check-log` at #272 (main 924d7cd
merged), not a current decline inventory. The counts follow "After the FingerprintException
burn-down" below, not the measurement above.

| Runs | Reason | Tests |
|---:|---|---|
| 63 | TLC 1.7.4 | `unit/check.test.ts:2573` ×5, `unit/check.test.ts:5133` ×3, `unit/check.test.ts:129` ×3, `unit/check.test.ts:1353` ×2, `unit/check.test.ts:2521` ×2, `unit/check.test.ts:5579` ×2, `unit/state-graph.test.ts:22` ×2, `unit/check.test.ts:5498` ×2, `unit/tlc-replay.test.ts:40` ×2, `unit/check.test.ts:2466`, `unit/check.test.ts:3519`, `unit/modules.test.ts:157`, `unit/check.test.ts:111`, `unit/check.test.ts:5541`, `unit/check.test.ts:1485`, `unit/liveness.test.ts:108`, `unit/modules.test.ts:152`, `unit/check.test.ts:5276`, `unit/check.test.ts:2508`, `unit/check.test.ts:2035`, `unit/check.test.ts:5363`, `unit/check.test.ts:1329`, `unit/check.test.ts:5440`, `unit/parallel.test.ts:18`, `unit/check.test.ts:5387`, `unit/check.test.ts:5293`, `unit/tlc-replay.test.ts:225`, `unit/check.test.ts:5416`, `unit/check.test.ts:5251`, `unit/check.test.ts:5468`, `unit/check.test.ts:5371`, `unit/check.test.ts:5256`, `unit/liveness.test.ts:122`, `unit/check.test.ts:5431`, `unit/check.test.ts:5401`, `unit/check.test.ts:5326`, `unit/check.test.ts:5482`, `unit/check.test.ts:5333`, `unit/check.test.ts:5283`, `unit/check.test.ts:2046`, `unit/tlc-replay.test.ts:185`, `unit/randomization.test.ts:162`, `unit/check.test.ts:5264`, `unit/check.test.ts:5424`, `unit/check.test.ts:2339`, `unit/check.test.ts:5454`, `unit/check.test.ts:1980`, `unit/tlc-replay.test.ts:167`, `unit/check.test.ts:5378` |
| 39 | dumping a value whose text depends on how TLC built it | `unit/native-sets.test.ts:86` ×38, `unit/native-builtins.test.ts:222` |
| 14 | the engine stopped: a constraint, a VIEW or an action property that fails on a successor | `unit/exit-codes.test.ts:10` ×3, `unit/tlc-replay.test.ts:40` ×2, `unit/check.test.ts:2983` ×2, `unit/check.test.ts:2071`, `unit/possible.test.ts:110`, `unit/check.test.ts:2013`, `unit/check.test.ts:2081`, `unit/check.test.ts:2026`, `unit/check.test.ts:2046`, `unit/check.test.ts:2002` |
| 11 | a constant invariant the engine checks, which TLC may warn about | `unit/engine.test.ts:46` ×3, `unit/engine.test.ts:807` ×2, `unit/bags.test.ts:43` ×2, `unit/exit-codes.test.ts:10`, `unit/engine-print.test.ts:31`, `unit/instances.test.ts:43`, `unit/tlc-replay.test.ts:197` |
| 11 | the engine declined: unsupported: Print | `unit/native-search.test.ts:1307` ×7, `unit/engine-print.test.ts:31` ×4 |
| 9 | an assumption that fails to evaluate: evaluating the assumption again: expected an integer, not a string | `unit/check.test.ts:3159` ×4, `unit/check.test.ts:2330` ×4, `unit/check.test.ts:2593` |
| 8 | -dump dot | `unit/state-graph.test.ts:22` ×8 |
| 6 | the engine stopped: a power set too large to build | `unit/engine.test.ts:1149` ×4, `unit/engine-print.test.ts:31`, `unit/engine.test.ts:680` |
| 5 | a POSTCONDITION or an ALIAS TLC may compute as it starts | `unit/alias.test.ts:72` ×2, `unit/possible.test.ts:123`, `unit/alias.test.ts:89`, `unit/possible.test.ts:118` |
| 5 | an assumption that fails to evaluate: evaluating the assumption again: integer overflow | `unit/check.test.ts:2330` ×5 |
| 5 | an assumption that fails to evaluate: evaluating the assumption again: SUBSET of a non-set | `unit/check.test.ts:2330` ×4, `unit/check.test.ts:2583` |
| 5 | the engine stopped: enumerated Nat | `unit/check.test.ts:3101` ×2, `unit/check.test.ts:1934` ×2, `unit/check.test.ts:1951` |
| 4 | a _POSSIBLE predicate the search didn't witness | `unit/check.test.ts:282`, `unit/possible.test.ts:66`, `unit/native-search.test.ts:1548`, `unit/native-search.test.ts:1541` |
| 4 | an assumption that fails to evaluate: evaluating the assumption again: expected an integer, not a set | `unit/check.test.ts:2330` ×4 |
| 4 | an assumption that fails to evaluate: evaluating the assumption again: it didn't fail | `unit/check.test.ts:2717`, `unit/check.test.ts:2330`, `unit/check.test.ts:2760`, `unit/check.test.ts:2754` |
| 4 | rebuilding a trace: the builtin Trace | `unit/alias.test.ts:48`, `unit/tlc-ext.test.ts:23`, `unit/alias.test.ts:59`, `unit/alias.test.ts:28` |
| 4 | the engine declined: unsupported: enumerating a set TLC keeps lazy (UNION at line 3) | `unit/native-sets.test.ts:269` ×3, `unit/native-sets.test.ts:332` |
| 4 | the engine stopped: division by zero: evaluating the failure again: the body of a function TLC keeps lazy | `unit/check.test.ts:1797`, `unit/check.test.ts:1809`, `unit/check.test.ts:1991`, `unit/check.test.ts:1980` |
| 4 | the engine stopped: recursion too deep | `unit/exit-codes.test.ts:10` ×3, `unit/check.test.ts:2928` |
| 4 | the engine stopped: unsupported: comparing a function TLC keeps lazy | `unit/native-search.test.ts:505` ×3, `unit/native-builtins.test.ts:228` |
| 4 | the engine stopped: unsupported: TLCGet of a key the search doesn't keep | `unit/tlc-statistics.test.ts:25`, `unit/check.test.ts:248`, `unit/check.test.ts:2837`, `unit/check.test.ts:5387` |
| 4 | values TLC can't compare, which the constant evaluator doesn't compute | `unit/check.test.ts:1257` ×3, `unit/exit-codes.test.ts:10` |
| 3 | -dump under SYMMETRY or a VIEW | `unit/native-search.test.ts:607`, `unit/native-search.test.ts:603`, `unit/native-search.test.ts:542` |
| 3 | a constant definition the configuration names | `unit/check.test.ts:5036`, `unit/check.test.ts:5028`, `unit/check.test.ts:5031` |
| 3 | a division by zero, which the constant evaluator doesn't compute | `unit/check.test.ts:5524`, `unit/check.test.ts:1300`, `unit/liveness.test.ts:122` |
| 3 | a property TLC finds a tautology | `unit/check.test.ts:5333`, `unit/check.test.ts:5211`, `unit/check.test.ts:5541` |
| 3 | a SYMMETRY definition that isn't an operator applied to its sets | `unit/check.test.ts:1243` ×2, `unit/exit-codes.test.ts:10` |
| 3 | an assumption that fails to evaluate: evaluating the assumption again: expected a sequence, not 1 | `unit/check.test.ts:2330` ×2, `unit/check.test.ts:2339` |
| 3 | an assumption that fails to evaluate: evaluating the assumption again: expected an integer, not a function | `unit/check.test.ts:2330` ×3 |
| 3 | an assumption that fails to evaluate: evaluating the assumption again: the builtin AssertEq | `unit/check.test.ts:770` ×2, `unit/json.test.ts:11` |
| 3 | printing a value whose text depends on how TLC built it | `unit/printing.test.ts:7` ×3 |
| 3 | temporal quantification in the specification | `unit/specifications.test.ts:68` ×2, `unit/exit-codes.test.ts:10` |
| 3 | the engine declined: unsupported: PickSuccessor | `unit/tlc-ext-operators.test.ts:11` ×2, `unit/tlc-ext-operators.test.ts:61` |
| 3 | the engine stopped: an order of strings the search ranked | `unit/native-builtins.test.ts:279` ×2, `unit/native-builtins.test.ts:327` |
| 3 | the engine stopped: applied a function outside its domain: evaluating the failure again: applied a function outside its domain | `unit/check.test.ts:1896`, `unit/check.test.ts:1874`, `unit/native-search.test.ts:505` |
| 1 | the engine stopped: deadlock | `unit/check.test.ts:2521` |
| 3 | the engine stopped: expected an integer: evaluating the failure again: expected an integer, not a string | `unit/tlc-replay.test.ts:40` ×2, `unit/exit-codes.test.ts:10` |
| 3 | the engine stopped: record compared with a function | `unit/engine.test.ts:46` ×3 |
| 2 | a constant part of a temporal formula that isn't a boolean | `unit/check.test.ts:5354` ×2 |
| 2 | a Java override that computes its value | `unit/overrides.test.ts:96`, `unit/overrides.test.ts:82` |
| 2 | a value that isn't a set where TLC wants one, which the constant evaluator doesn't compute | `unit/check.test.ts:5579` ×2 |
| 2 | an assumption that fails to evaluate: evaluating the assumption again: applied a function outside its domain | `unit/check.test.ts:2692`, `unit/check.test.ts:2695` |
| 2 | an assumption that fails to evaluate: evaluating the assumption again: SubBag's >=, which may be Naturals' or Integers' | `unit/bags.test.ts:97`, `unit/check.test.ts:501` |
| 2 | an assumption that fails to evaluate: evaluating the assumption again: TLCGet | `unit/tlc-revision.test.ts:26`, `unit/tlc-action.test.ts:10` |
| 2 | an operator, which the constant evaluator doesn't compute | `unit/check.test.ts:5354`, `unit/engine-ir.test.ts:190` |
| 2 | SANY's report of a module-level RECURSIVE declaration that something else binds, or an INSTANCE may: F | `unit/check.test.ts:4626`, `unit/check.test.ts:3442` |
| 2 | the engine declined: the builtin EmptyBag@Bags, whose value the interpreter computes | `unit/modules.test.ts:136` ×2 |
| 2 | the engine declined: unsupported: enumerating a set TLC keeps lazy (UNION at line 5) | `unit/native-sets.test.ts:343`, `unit/check.test.ts:1606` |
| 2 | the engine declined: unsupported: F | `unit/operator-constants.test.ts:34` ×2 |
| 2 | the engine declined: unsupported: PrintT | `unit/tlc-constraint-order.test.ts:11`, `unit/tlc-statistics.test.ts:11` |
| 2 | the engine stopped: a guard that isn't a boolean: evaluating the failure again: a next-state relation the IR holds no actions of | `unit/exit-codes.test.ts:10`, `unit/check.test.ts:2961` |
| 2 | the engine stopped: an invariant violated | `unit/check.test.ts:644`, `unit/check.test.ts:2521` |
| 2 | the engine stopped: equality of values TLC can't compare: evaluating the failure again: equality of values TLC can't compare | `unit/check.test.ts:1416` ×2 |
| 2 | the engine stopped: Print inside ENABLED | `unit/engine-print.test.ts:31`, `unit/native-search.test.ts:1315` |
| 2 | the engine stopped: printing where the native checker doesn't check the temporal properties: prints it doesn't place in TLC's order | `unit/native-search.test.ts:1059`, `unit/native-search.test.ts:1075` |
| 2 | the engine stopped: TLCExt's Trace, the behavior the engine doesn't keep | `unit/tlc-ext.test.ts:17`, `unit/tlc-ext.test.ts:30` |
| 2 | the engine stopped: ToString of a text the engine made unranked | `unit/native-builtins.test.ts:491`, `unit/native-builtins.test.ts:279` |
| 2 | the engine stopped: unsupported: a state holding a function TLC keeps lazy | `unit/check.test.ts:1963`, `unit/check.test.ts:1934` |
| 2 | the engine stopped: values TLC can't compare: evaluating the failure again: a failure TLC reports as a FingerprintException | `unit/check.test.ts:1675` ×2 |
| 2 | the Java overrides TLC lists in the JVM's order | `unit/engine-ir.test.ts:144`, `unit/overrides.test.ts:16` |
| 1 | -dump with temporal properties | `unit/native-search.test.ts:711` |
| 1 | a CHOOSE no element of which satisfies, which the constant evaluator doesn't compute | `unit/check.test.ts:1290` |
| 1 | a configuration error that shows a value | `unit/check.test.ts:5044` |
| 1 | a configuration substitute with effects, which TLC evaluates at every use: C <- Foo | `unit/check.test.ts:1040` |
| 1 | a Java override class with a static initializer | `unit/overrides.test.ts:82` |
| 1 | a Java override class with a superclass | `unit/overrides.test.ts:82` |
| 1 | a Java override class with annotations | `unit/overrides.test.ts:82` |
| 1 | a Java override class with fields | `unit/overrides.test.ts:82` |
| 1 | a Java override class with methods of one name | `unit/overrides.test.ts:82` |
| 1 | a Java override of a name TLC maps to an operator's | `unit/overrides.test.ts:82` |
| 1 | a Java override with parameters, whose arguments TLC evaluates | `unit/overrides.test.ts:59` |
| 1 | a temporal property's counterexample: a step back into the cycle of a spec that prints | `unit/counter-example.test.ts:11` |
| 1 | a violating successor TLC fails to find again from its generator | `unit/randomization.test.ts:41` |
| 1 | an ALIAS without a definition | `unit/alias.test.ts:72` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: a power set too large to build | `unit/check.test.ts:3084` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: a SelectSeq test that isn't a boolean | `unit/check.test.ts:2330` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: enumerated an infinite set | `unit/check.test.ts:2675` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: evaluating a an unbounded quantifier | `unit/check.test.ts:1473` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: expected a boolean, not a set | `unit/check.test.ts:2675` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: expected a sequence, not "ab" | `unit/check.test.ts:2330` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: expected a set, not a integer | `unit/check.test.ts:2675` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: expected an integer, not a boolean | `unit/check.test.ts:2330` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: recursion too deep | `unit/exit-codes.test.ts:10` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: the builtin ToJson@Json | `unit/modules.test.ts:152` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: the builtin Trace | `unit/tlc-ext-operators.test.ts:11` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: values TLC can't compare | `unit/check.test.ts:3248` |
| 1 | no step from state N is the trace's next | `unit/check.test.ts:721` |
| 1 | SANY's report of a RECURSIVE declaration of a name a module binds or names before it: F | `unit/check.test.ts:4677` |
| 1 | several states TLC may take for the search's under VIEW or SYMMETRY | `unit/native-search.test.ts:870` |
| 1 | the engine declined: checking an assumption again: an assumption the engine doesn't evaluate that fails to: AssertError of a message that isn't a string | `unit/tlc-ext-operators.test.ts:69` |
| 1 | the engine declined: checking an assumption again: an assumption the engine found to hold that doesn't again | `unit/json.test.ts:11` |
| 1 | the engine declined: record compared with a function | `unit/native-search.test.ts:1520` |
| 1 | the engine declined: unsupported: a value TLC computed at startup with effects | `unit/native-search.test.ts:1642` |
| 1 | the engine declined: unsupported: AssertEq | `unit/tlc-ext-operators.test.ts:11` |
| 1 | the engine declined: unsupported: enumerating a lazy set of the state under a VIEW | `unit/check.test.ts:2155` |
| 1 | the engine declined: unsupported: enumerating a set TLC keeps lazy (Alias: UNION at line 5) | `unit/native-sets.test.ts:354` |
| 1 | the engine declined: unsupported: expression UnboundedQuantifier | `unit/bundled-modules.test.ts:16` |
| 1 | the engine declined: unsupported: Inc | `unit/operator-constants.test.ts:17` |
| 1 | the engine declined: unsupported: Print where TLC evaluates it otherwise | `unit/native-search.test.ts:1307` |
| 1 | the engine declined: unsupported: RandomElement | `unit/randomization.test.ts:142` |
| 1 | the engine declined: unsupported: TLCGetAndSet | `unit/tlc-ext-operators.test.ts:94` |
| 1 | the engine declined: unsupported: UNCHANGED in the initial predicate | `unit/native-search.test.ts:1397` |
| 1 | the engine declined: unsupported: walking a lazy function over a tuple | `unit/check.test.ts:1830` |
| 1 | the engine stopped: a conjunct that isn't a boolean: evaluating the failure again: expected a boolean, not a integer | `unit/check.test.ts:2368` |
| 1 | the engine stopped: a tuple pattern that doesn't match: evaluating the failure again: a tuple pattern that doesn't match | `unit/native-search.test.ts:1361` |
| 1 | the engine stopped: a VIEW that fails on an initial state | `unit/engine-symmetry.test.ts:25` |
| 1 | the engine stopped: an atom of the temporal properties that may fail to evaluate | `unit/engine.test.ts:1149` |
| 1 | the engine stopped: an invariant violated: a _POSSIBLE predicate | `unit/possible.test.ts:72` |
| 1 | the engine stopped: an order of model values the search ranked | `unit/native-builtins.test.ts:315` |
| 1 | the engine stopped: an overflow counting the elements of a power set: evaluating the failure again: an action that fails or prints after a successor TLC can't fingerprint | `unit/check.test.ts:2137` |
| 1 | the engine stopped: an overflow counting the elements of a power set: evaluating the failure again: it didn't fail | `unit/check.test.ts:2121` |
| 1 | the engine stopped: applied a function outside its domain: evaluating the failure again: values TLC can't compare | `unit/check.test.ts:2573` |
| 1 | the engine stopped: applied a function outside its domain: rebuilding a trace: primed variable not assigned: x | `unit/native-search.test.ts:1461` |
| 1 | the engine stopped: applied a non-function: evaluating the failure again: applied a non-function: {1, 2} | `unit/check.test.ts:1627` |
| 1 | the engine stopped: BagOfAll of a literal | `unit/native-builtins.test.ts:228` |
| 1 | the engine stopped: CHOOSE found no element: a failure in a model with temporal properties | `unit/tlc-replay.test.ts:40` |
| 1 | the engine stopped: division by zero | `unit/check.test.ts:2508` |
| 1 | the engine stopped: division by zero: a failure in a model with temporal properties | `unit/tlc-replay.test.ts:40` |
| 1 | the engine stopped: division by zero: a failure with a POSTCONDITION | `unit/possible.test.ts:110` |
| 1 | the engine stopped: drew from a set whose shape the engine forgets | `unit/native-builtins.test.ts:417` |
| 1 | the engine stopped: enumerated [D -> R] with R infinite | `unit/native-sets.test.ts:169` |
| 1 | the engine stopped: enumerated a non-set: a failure in a model with temporal properties | `unit/check.test.ts:2489` |
| 1 | the engine stopped: enumerated a product of an infinite set | `unit/native-sets.test.ts:169` |
| 1 | the engine stopped: enumerated an infinite set | `unit/native-sets.test.ts:169` |
| 1 | the engine stopped: enumerated an operation on infinite sets | `unit/bundled-modules.test.ts:23` |
| 1 | the engine stopped: equality of values TLC can't compare: evaluating the failure again: a failure TLC reports as a FingerprintException | `unit/check.test.ts:1416` |
| 1 | the engine stopped: EXCEPT outside the domain | `unit/check.test.ts:1627` |
| 1 | the engine stopped: expected a boolean: evaluating the failure again: enumerated a lazy filter | `unit/native-sets.test.ts:169` |
| 1 | the engine stopped: expected a boolean: evaluating the failure again: expected a boolean, not a function | `unit/check.test.ts:1403` |
| 1 | the engine stopped: expected a function: evaluating the failure again: BagIn of a value that isn't a function | `unit/native-builtins.test.ts:228` |
| 1 | the engine stopped: expected a function: evaluating the failure again: SubBag of a value that isn't a function | `unit/native-builtins.test.ts:228` |
| 1 | the engine stopped: expected an integer: evaluating the failure again: SubBag's >=, which may be Naturals' or Integers' | `unit/native-builtins.test.ts:228` |
| 1 | the engine stopped: printing where the native checker doesn't check the temporal properties: a node that accepts every behavior | `unit/native-search.test.ts:1047` |
| 1 | the engine stopped: printing where the native checker doesn't check the temporal properties: a predicate the engine leaves to the interpreter | `unit/check.test.ts:2466` |
| 1 | the engine stopped: printing where the native checker doesn't check the temporal properties: steps from states it didn't store | `unit/native-search.test.ts:826` |
| 1 | the engine stopped: RandomSubset of a product too large to index | `unit/native-builtins.test.ts:390` |
| 1 | the engine stopped: RandomSubset of an interval too large to draw from | `unit/native-builtins.test.ts:401` |
| 1 | the engine stopped: TLCGet of a key that isn't a natural number | `unit/check.test.ts:2837` |
| 1 | the engine stopped: TLCGet of a register TLC hasn't set | `unit/check.test.ts:2837` |
| 1 | the engine stopped: unsupported: TLCGet("diameter") in the search | `unit/check.test.ts:248` |
| 1 | the engine stopped: unsupported: TLCSet of a key that stops or configures TLC | `unit/tlc-pause.test.ts:8` |
| 1 | the engine stopped: values TLC can't compare: evaluating the failure again: a set TLC leaves unnormalized | `unit/native-builtins.test.ts:228` |
| 1 | the liveness checker declined: a late node TLC adds at another diameter | `unit/native-search.test.ts:1104` |
| 1 | the liveness checker declined: an atom the engine doesn't answer | `unit/native-search.test.ts:1107` |
| 1 | TLCGet, which the constant evaluator doesn't compute | `unit/check.test.ts:1034` |

### After the CLI's flip (measured 2026-11-11)

Measured at main 8165d917, after #224 flipped the CLI, with `bun scripts/run.ts check-log`:

- 1,887 checks. 1,386 print TLC's output natively and 501 are not native yet. None answered
  differently on one thread and four.
- In TLC's default mode, which writes the trace exploration spec, 245 are native. The rest wait on
  SANY's report of that spec, which the XML session owns with the other SANY reports.

What the 501 decline at, grouped by the mechanism that would make them native. "Reasons" counts the
distinct decline messages in the group.

| Mechanism | Runs | Reasons | Owner |
|---|---:|---:|---|
| Values whose text depends on how TLC built them, and sets TLC keeps lazy | 82 | 12 | S1 (lazy-values, after the memo session's guard) |
| A failure TLC words as a FingerprintException | 70 | 14 | fingerprint session |
| TLC 1.7.4 | 63 | 1 | retired: declines until the TypeScript goes |
| An assumption that fails to evaluate, evaluated again | 57 | 25 | front session |
| Temporal properties and liveness | 50 | 19 | liveness session |
| The engine stopping where TLC reports an error | 48 | 27 | memo session |
| What the constant evaluator doesn't compute | 14 | 3 | front session |
| Other failures evaluated again | 29 | 18 | memo session |
| The engine declining an operator or builtin | 14 | 11 | memo session |
| Print and PrintT where the engine can't place them | 16 | 4 | S1 (lazy-values) |
| `-dump` (`dot`, and under SYMMETRY or a VIEW) | 12 | 3 | S2 |
| Java overrides TLC loads with more than the shapes ported | 9 | 8 | unassigned |
| SANY's report of RECURSIVE declarations | 4 | 3 | XML session |
| The rest: a configuration substitute with effects, states TLC may take for the search's under VIEW or SYMMETRY, and a trace the search can't step | 4 | 3 | unassigned |

The groups are checked in this order, so a decline counts once, in the first group that takes it.
The constant evaluator's row and the Java overrides' row count what was left after the
front-constants branch (measured 2026-11-11 from b8121dd3, 1,452 native before and 1,473 after):
it made native the CHOOSE, division, equality, quantifier-bound and INIT or NEXT constant
declines, and an annotated override and one that catches, and moved TLCGet("level") as a
substitute to "a configuration substitute with effects" among the rest.
The startup checks after it (measured 2026-11-11 from ee6736a4, 1,499 native before and 1,512
after) made native the SYMMETRY definitions TLC fails on, the configuration error that shows a
set, the successor TLC fails to find again from its generator, and the constant invariants TLC
warns about, but one that overflows TLC's stack and one that fails as a set operation. The
constant conjunct of the specification that draws at random moved to the engine's decline of
RandomElement under a comparison.
The TLCExt builtins after it (measured 2026-11-11 from 924d7cde, 1,478 native before and 1,482
after) made native AssertEq, UNCHANGED in the initial predicate and PickSuccessor where TLC answers
without asking, and moved TLCGetAndSet's run and the interactive PickSuccessor to the engine's
stops.
The 1.7.4 runs leave with the TypeScript, and `check-log` now counts them apart, as retired with
the interpreter, without running them. The other 438 block deleting the interpreter, with native
progress events for the library's `onProgress` (see "The public API afterwards").

#### Declines to win back

Checks the binary answered and now declines, because the answer matched TLC only by chance.

- **Paths on Windows** (PR 364): where TLC on Windows would print a path whose rendering no run
  of TLC on Windows has recorded, the binary declines. They were printed with `/` and could only
  have matched TLC by chance. Winning each back takes recording TLC on Windows.
  - **The trace exploration spec**, whose path TLC prints and whose trace file it names in the spec
    with Java's `Path.toString` (`the path TLC prints on Windows of the trace exploration spec`): a
    violation of more than one state in TLC's default mode declines on Windows unless `-noTE` is
    given. The library's `check` writes no such spec unless `isTraceRecorded` asks for one, so it
    answers violations on Windows as elsewhere (`tests/unit/native-check.test.ts`).
  - A module found by a path other than its real one, whose `(file:…)` URL Java writes with
    `File.toURI` (`the URL TLC prints on Windows of a module whose path isn't its real one`), as a
    working directory that is a short (8.3) path or reached through a link makes of every module.
  - A module in the root module's file (`the path TLC prints on Windows of a module in the root
    module's file`), and a standard module from a jar on the class path (`the URL TLC prints on
    Windows of a standard module in its jar`).
  - A Java override's class (`the URL TLC prints on Windows of a Java class`), and TLC 1.7.4's
    paths.

  `get_windows_expectation` in tests/common/mod.rs gives each path test's Windows expectation from
  the Unix recording.

- **The library where the check stops before it searches without a typed error** (PR 7): a
  decimal or big literal the front end rejects, and a big number in the configuration, which it
  words otherwise than TLC or rejects where TLC doesn't (see "Known wrong outputs"), and a stop
  after SANY printed a warning, which the library would print before it throws. The binary prints
  its output, but `get_thrown` returns nothing, so `check` throws `TlaUnsupportedError` "not
  native yet: the engine stopped before it searched (exit N)" where the interpreter threw its own
  error. Won back: SANY's fatal errors (a module it can't find or parse, a file named after
  another module, a circular dependency), which `check` throws as `TlaSyntaxError` with SANY's
  report; and the other configuration and evaluation errors TLC reports before it searches (a
  configuration file it can't parse, a SYMMETRY that isn't a set of permutations, a temporal
  formula it can't handle or whose constant part fails, a stack overflow, an exception as it
  starts), which `check` throws as `TlaConfigError`, `TlaEvaluationError` or
  `TlaStackOverflowError` with TLC's message, after what the spec printed as TLC computed its
  constants. 205 of the 214 such errors `bun run test` throws are TLC's error and prints, run
  against TLC at d8fb231; the others are listed under "Known wrong outputs", or are TLC's warnings
  TLC prints before the error, which `onPrint` doesn't get, or TLC's call stack after a stack
  overflow, which `TlaStackOverflowError` doesn't hold.

- **A set operation whose operand is a lazy set of values TLC fails to compare, or has effects**
  (#362), 140 cells of `unit/union-grid.test.ts` that matched on main. TLC builds both operands of
  `\cup`, `\cap` and `\` before it tests either (OPCODE_cup), so the engine now builds them too.
  - 104 cells, such as `1 \in {1, 2} \cup SUBSET {1, "a"}` (and likewise with `[a : S]`, `S \X T`
    or `[S -> T]` of such values on the right): building `{1, "a"}` stops the engine, where it
    answered from the left operand alone.
  - 36 cells with an operand that prints or sets a register: building an operand and then testing
    it would evaluate it twice, so the engine stops before it evaluates either.
  - TLC reduces a `\cup`, `\cap` or `\` of a set enumeration or an interval as it evaluates it,
    testing one operand's elements in the other (`Reducible.cup`, `cap` and `diff`), so a
    membership in the result, or in a set that holds it, runs those tests too, and stops where an
    operand has effects, since they evaluate it again. The grid of reduced operations in
    `unit/union-grid.test.ts` (1,944 cells: each operation on two of nine operands, alone and
    held in unions another operand answers) has 0 wrong verdicts, against 242 on main; 10 of its
    cells decline, each a difference from a record's domain that declined on main too.
  - Two runs of the upstream tla-ts suite that matched before #362 decline since: an assumption
    that fails in the body of a function TLC keeps lazy, where the evaluator can't tell the key
    TLC evaluates (`F = F` of a recursive function that fails at a key), and
    `ValueSemanticsAssume` run with warnings on, whose EXCEPT of a missing key TLC warns of.
  - An operand with effects that a name binds, as a LET definition or an operator's argument
    does, stops the engine before it evaluates either operand, as one written in place does;
    should an effect run all the same as the membership builds or tests its operands, it stops
    there. The grid's 19 such cells print as TLC does but one, which sets a register and
    declines: `LET S == {IF TLCSet(1, TLCGet(1) + 1) THEN <<1, 1>> ELSE <<0, 0>>} IN
    <<1, 1>> \in S \cup ({1} \X {1})`, which matched on main.

- **Strings made during the search** (the string-order change; check-log on the same log, 1386
  native on main, 1384 after): `unit/check.test.ts:704` and `unit/parallel.test.ts:18` with
  `-workers 2`, both `fixtures/strings/RuntimeStrings`, where `CHOOSE` picks among
  `"q" \o ToString(n)` strings the search makes. TLC orders two strings by when it interned them,
  and it interns a string the search makes as it makes it. The store ordered two that no rank covers
  by their text, which matched TLC's creation order there by chance. It now stops on them (`an order
  of strings the search made`), and the library's tests assert TLC's output through the interpreter.
  Winning them back takes the engine ranking what it makes in TLC's order of evaluation: one worker,
  every successor and every expression in TLC's order, which a later change would have to show.
- **Live progress during a native check.** The native check reports `onProgress`'s events once it
  ends, where the TypeScript check reported them as the search reached them. Live delivery would
  take a callback the check calls as the printer prints: a threadsafe function in the napi binding,
  since the check runs on its own thread, and an import in the WebAssembly binding. `checkSources`
  reruns the check from the start each round it needs another file, so the events of a round may
  go out only once it is the last: the library would hold them until the check returns without
  asking for more, or the check would ask for every file before it searches.

### After the FingerprintException burn-down (measured 2026-11-11)

Measured at #272 (main 924d7cd merged) with `bun scripts/run.ts check-log`:

- 1,895 checks. 1,495 print TLC's output natively and 400 are not native yet, for 147 reasons,
  listed in full under "Every reason" above. None answered differently on one thread and four.
- The declines TLC words as a FingerprintException went from 69 runs to 3: "values TLC can't
  compare" (2) and "equality of values TLC can't compare" (1).
- In TLC's default mode, which writes the trace exploration spec, 1,044 are native.

SANY's report of RECURSIVE declarations is native from #266, which takes SANY's messages from
its generator where linking declines. Measured with `check-log` at that PR's head 04c7267: none of
the 4 runs declines; of 1,891 checks, 1,456 are native and 435 not native yet, with 0 answered
differently on one thread and four, and 1,020 are native in TLC's default mode.

### Java overrides that stay declined

The front end reads the class TLC loads for a module and puts the constant each method returns in
place of the operator. It skips a method annotated `@TLAPlusOperator` or `@Evaluation`, as
`processModuleOverrides` does, and runs a method that catches an exception up to its first return.
It declines an annotated method where a `tlc2.overrides.TLCOverrides` index, beside the spec or at
its package's path, could load the class.

It reads the index itself (`get_index_targets`), as `processModuleOverrides` loads it from
`tlc2/overrides/TLCOverrides.class` (a file named `tlc2.overrides.TLCOverrides.class` only
locates the directory the class loader reads that path in, and TLC skips a class that implements
no interface): the classes its `get` returns, by class literal or by `Class.forName` of a string
constant, and in each the methods annotated `@TLAPlusOperator`, `@Evaluation` or
`@TLAPlusCallable`. Each such method replaces the body of the operator its module's
`ModuleNode.getOpDef` finds by name, and (for `@TLAPlusOperator`) arity. That searches the
module's whole context: its own and LOCAL definitions and those EXTENDS, INSTANCE and LOCAL
INSTANCE bring in, so `module="M"` for the root that extends `TLC` replaces `TLC!Any`, and
`module="TLC"` replaces Naturals' `+`, which TLC instantiates. The front end resolves the name in
the module's scope (a standard module's with the modules it extends or instantiates) and
replaces the definition in the module that wrote it, and every copy of it, which share its body.
The name is SANY's: `\leq` replaces `<=`, while `<=`, `=<` or `#`, which SANY gives no operator,
replace nothing. A method whose module SANY didn't load, or whose operator it doesn't define,
replaces nothing. A replaced definition becomes a declined builtin
(`decline_index_overrides`, `Builtin::INDEX_REPLACED`), which declines where the front end or
the engine evaluates it (`an operator a TLCOverrides index's Java method replaces`), so a dead
branch, a short-circuited operand or an ALIAS that is never printed still runs, as does a
replaced body that would print, which TLC never evaluates. A replaced standard operator, which the engine computes as a
builtin whatever its flags, declines the spec wherever what TLC evaluates names it
(`get_reached_key`): `an operator a TLCOverrides index's Java class replaces: TLC!Any`. A
definition without parameters no part of the model reads, which TLC computes as it starts
(`processConstantDefns`) and whose value or exception it drops, is no such name, unless the
method may print, exit or loop: one that does more than make a value of TLC's or throw
(`is_quiet_code`) declines wherever a definition TLC computes as it starts reaches it (`a
TLCOverrides index's Java method that a definition TLC computes as it starts may call`).
It also declines, whether or not the model evaluates the operator:

- an index whose code does more than build its array from class literals and `Class.forName`
  (`a TLCOverrides index whose classes the front end doesn't read`), that implements an
  interface other than `ITLCOverrides` or has a superclass, that names a class not beside the
  spec (a class literal of the JDK's, which declares no operator, replaces nothing), that holds
  a null `get` returns or its array holds, or that isn't public or has no public constructor
  without parameters, which `newInstance` fails on;
- a name of a copy a named INSTANCE makes (`I!Op`, `an INSTANCE's operator a TLCOverrides index's
  Java method replaces`), and an operator of an inner module (`an inner module's operator a
  TLCOverrides index's Java method replaces`);
- a method whose operator the front end finds neither by name in its module's scope nor as a
  builtin (`an operator a TLCOverrides index's Java method replaces that the front end doesn't
  resolve`);
- a listed class with a superclass, an interface, or a static initializer `Class.forName` runs;
- a method TLC reports, with `warn` left true, or a `@TLAPlusCallable` or non-silent
  `@Evaluation` that replaces an operator;
- a replacement TLC calls or fails on as it starts: a `final` `@TLAPlusOperator` method without
  parameters (`MethodValue.get`), a method `MethodHandles.publicLookup` can't reach, and an
  `@Evaluation` of a standard module's operator (`a TLCOverrides index's Java method TLC calls as
  it starts, or can't call`);
- a replaced operator the configuration names, as INIT, an invariant or any other entry, or as
  a substitute's target, which TLC reads from `defns`, where the index's method is (`an operator
  a TLCOverrides index's Java method replaces that the configuration names`), or assigns a value
  in a module (`Make = [Aux] 2`), over which TLC keeps the method. A global value or substitute
  replaces the method in TLC, as it does the definition natively. For a builtin of TLC's, as
  `TLC!Any` with `CONSTANT Any = {2}` (`index-global-any`), `processSpec` gives the value to the
  root's OpDefNode, which `lookup` reads before the body that holds the method, and the front
  end reads the value in place of the builtin; an INSTANCE's copy (`LOCAL INSTANCE TLC` in a
  module, `I == INSTANCE TLC`, a LET's) is another node, whose body still holds the method (TLC
  fails on `1 \in 7`), so the builtin still declines (`an operator a TLCOverrides index's Java
  class replaces`, `index-global-any-instanced`) where a module holds an unnamed INSTANCE of TLC,
  a LET holds one, or a name written with a module's INSTANCE's prefix (`I!Any`) reads it, as
  does another standard module's builtin, whose copies other standard modules make. An
  INSTANCE of another module, even one that extends TLC (`N1 == INSTANCE N`, N `EXTENDS TLC`
  with `NA == Any`, reads {2}), and an INSTANCE of TLC whose copy nothing names answer. main
  never reads the copy (wrong on `1 \in I!Any`, `LET I == INSTANCE TLC IN 1 \in I!Any` and a
  module's `LOCAL INSTANCE TLC` read), so it matches a LET's INSTANCE of TLC that nothing TLC
  evaluates reads only by chance (`U == LET I == INSTANCE TLC IN I!Any` unread, or `1 \in Any
  /\ I!Any # {}`, whose first conjunct decides), which still declines.

These shapes stay
declined for good, because what TLC does with them depends on the JVM, not on the class file:

- **A static initializer, a field's initializer or a superclass.** Java runs them as TLC first
  calls a method, and what they print or throw shows in TLC's output. A failure there is an
  `ExceptionInInitializerError`, whose report holds the JDK's own stack frames.
- **A value the method computes by calling the JDK,** such as `Integer.parseInt`, which the front
  end would have to run as Java does.
- **Several methods TLC reports.** `Class#getDeclaredMethods` lists them in the order HotSpot
  allocated the symbols of their names, which changes with `-Xshare:off` on the same JDK, and TLC
  prints a message for each in that order. Where two methods share a name, the one listed last
  overrides the other. The binary declines a class whose methods print more than one message, or
  that has methods of one name, wherever the order could change what TLC logs.

A method whose name `TLARegistry.mapName` maps to an operator's, such as `Plus` to `+`, is declined
for now, not for good: the standard modules whose classes register the names are those SANY
parsed before the overriding module, which in TLC's default mode include the modules of the trace
exploration spec. With `-noGenerateSpecTE` and no EXTENDS, TLC at d8fb231 loads `Plus` as `Plus`,
and in the default mode it fails to match it as `+`.

### What uses it as the reference, and what replaces it

| User | Replacement |
|---|---|
| Unit tests of the interpreter's internals (about 30 cases) | Deleted with the code; `enumeration-oracle` keeps native against TLC's frozen answers; `engine-store` and `engine-fingerprints` check the native store against `ValueOracle` |
| Unit tests that compare the engine with the interpreter (about 200 cases: `native-search`, `native-sets`, `native-builtins`, `engine*`, the `PROVE_IT_ENGINE=0` runs in `check` and `cli`) | Golden output recorded once from TLC at d8fb231, as the existing fixture `.out` files are; `compareStateLogs` becomes 1 thread against 4 plus TLC's counts |
| `differential.ts` pairs `rust/interpreter` and `rust/stopped` | Gone with the hand-over they test; `tlc/rust` and `tlc/native` against `tlc-stdout` stay |
| `engine-coverage.ts`'s run with the engine off | Dropped; `expected.json` judges the outcome |
| `value-oracle.ts`'s interpreter fingerprints and TypeScript store | Dropped; TLC's classes stay the oracle |
| `front-differential.ts`'s TypeScript side | Goes with the TypeScript front end |
| Verification's Packages and Binary checks with `PROVE_IT_ENGINE=0` | Checks of the WebAssembly engine in `dist` |

The 39 passing models TLC takes more than 20 s on have outcome recordings in `expected.json` but
no full `tlc-stdout`. Recording them is deferred.

### Stages

- **S0. The front end.** `tla-front` replaces the TypeScript SANY front end and `ir.ts` in the
  library, and the addon and the WebAssembly module take module sources through a loader callback.
  This is the front end's workstream.
- **S1. The binary's check as a host entry.** First, as a pure refactor, `prove-it-cli`'s check
  driver moves into a crate the binary and `prove-it-host` share. `tla-trace` and `tla-live` print
  through a sink, not stdout, and the driver returns a structured outcome (status, counts,
  violation, trace states) beside the lines. The binary must stay byte-identical. Then
  `check_sources` takes sources through S0's loader. `native.ts` and `wasm.ts` call it, and the
  library flips once `tlc/rust` equals `tlc/native` on all 1466 runs. That removes the 15 declines
  and the 131 hand-overs together.
- **S2. The interpreter-only features, built natively:** `-dump` (which `state-graph`'s tests also
  need), `-continue`, periodic configs and TLC 1.7.4's output, each after measuring how often the
  tests and the corpus use it; and `tla-live`'s declines, where a test or a model meets one. For
  WebAssembly's stack, see the measurement below.
- **S3. Tests on TLC's recordings,** recorded once with a recorder script.
- **Native progress events (done).** The native check records each message TLC prints, with its
  code, its place among the spec's prints and, for a check of the temporal properties part way
  through the search, the search's counts; `check` turns them into `CheckProgress` events
  (`src/native-progress.ts`), which it reports once the check ends. On the corpus models the native
  check answers, the events and their order equal the TypeScript check's (746 of the 762 it answers
  of 920; of the other 16, six were the report of a violation, fixed since, five the clock's, one
  a warning below, and four differed in the result or the prints: TLC's recordings side with the
  native check on Github696b's error and VoteProof's deadlock, where the TypeScript check differs,
  and the two UserModuleOverride models printed what the property prints as TLC finds the behavior
  violating it only through the TypeScript check, which the native check's `onPrint` now
  receives too), but for
  the events TLC schedules by the clock: natively a caller gets a `progress` event for each report
  the native search made, every minute, and a `liveness-started` with `isComplete` false for each
  check part way through it, at the native search's own times. Where the two differ otherwise:
  - `liveness-initializing` takes `isSymmetric` and `isConstrained` from the configuration, as
    TLC warns, where the TypeScript check first drops a constraint that is a constant formula and
    a symmetry whose sets are too small;
  - a name the configuration lists twice gets the warning event TLC prints, which drops a warning
    identical to one it printed (`MP.printWarning`), where the TypeScript check reports it twice;
  - with `-nowarning`, the native check reports none of the warnings TLC doesn't print, where the
    TypeScript check still reports a constant-level invariant, a state-level property and a
    symmetry set too small;
  - what the native engine doesn't print yet has no event either: the warning of an EXCEPT on a
    record's missing field in an ASSUME or an ALIAS, and what the spec prints as TLC searches for a
    liveness counterexample;
  - `PROVE_IT_TEST_LIVE_CHECK_AT` names the state before whose expansion the native search checks,
    and after whose expansion the TypeScript check does.
- **S4. Flip and delete.**
  - `check` loses the interpreter tier, `PROVE_IT_ENGINE=0` and `PROVE_IT_LIVE_CHECK`.
  - About 24,000 lines go: `evaluate`, `values`, `environment`, `successors`, `search`, the
    interpreter's part of `check`, `liveness*`, `tableau`, `state-graph`, `builtins`, `bags`,
    `java-overrides`, `parallel*`, `worker`, `fingerprints`, `symmetry`, `randomization`,
    `transfer`, `dependencies`, `codegen`, `runtime`, `instances`, `subexpressions`,
    `spec-description`, the rest of `tlc/`, and `engine/store`, `convert`, `fingerprint`,
    `native-store` and `ir`.

### WebAssembly's stack (measured 2026-11-10)

WebAssembly's frames are on the host's stack, so a deep recursion there traps where the addon's
search thread doesn't.

- **The corpus.** The 733 Conformance models were run with the engine as WebAssembly, three
  ways: under Node with Parity's `--stack-size=8000`, under Node's default stack, and under Bun.
  No model trapped in any of the three, and each tier matched the addon's run model by model.
- **The depth.** `F(n) == IF n = 0 THEN 0 ELSE 1 + F(n - 1)` holds to about 15,000 calls under
  Node with `--stack-size=8000`, 1,800 under Node's default stack, and 1,500 under Bun, which has
  no flag to raise it. The addon recurses to the engine's bound of 3,000 (20,000 when this was
  measured; see "A recursion without end"). TLC's JVM overflows at a few hundred to a few thousand.
- **The choice.** The engine as WebAssembly stops at 1,000 calls (`MAXIMUM_RECURSION`) and
  declines the model, so that a recursion never traps there. A trap that a deeper frame still
  causes declines too (`checkSources` in `wasm.ts`). A larger stack in a Worker, which Node alone
  offers, is optional, and an explicit stack in the evaluator isn't worth its size.
- **The library's answer.** Where the engine as WebAssembly stops at its bound
  (`recursion deeper than WebAssembly's stack holds`) or traps, the library's check throws
  `WebAssemblyStackError`, which names the addon and the binary, rather than search again in the
  interpreter. So a model that recurses between 1,000 and 3,000 calls is checked with the addon
  and the binary and rejected as WebAssembly: `native.test.ts` pins both answers.

### The CLI flipped

The CLI runs each TLC command line through `checkSources` first (`checkNatively` in
`src/cli/tlc.ts`) and prints what the binary prints. Where the binary declines the model, where no
engine loads, or with `PROVE_IT_ENGINE=0`, it checks the spec as before.

What the check prints is held until the check ends. It can decline part way through the search:
- a print the relay can't word;
- a periodic configuration at its first check;
- a trace or failure the trace evaluator can't rebuild;
- the temporal properties at the end.

A model the CLI then checks the old way prints only once. Streaming waits until those declines
are few.

TLC writes a trace exploration spec unless `-noGenerateSpecTE` says not to, and the binary
doesn't yet write SANY's report of the spec TLC parses with it. So without that option, most runs
still go the old way. The corpus and the differential pass it.

What the CLI's runs declined at the flip (`bun test tests/unit` and the 733 corpus models, each
run with and without `-noGenerateSpecTE`):

| Kind | CLI test runs | Owner |
|---|---:|---|
| `java -cp …jar tlc2.TLC`: reading the version of a tla2tools.jar | 117 | the CLI (prove-it-check) |
| SANY's report of the trace exploration spec | 64 test runs, 664 corpus runs | the front end |
| TLC 1.7.4's output | 5 | retired: it declines until the TypeScript goes |
| `-dump`, `-continue` | 7 | S2 |
| the 518 of the library's `check` calls, by mechanism (above) | the rest | as staffed |

Since then, the binary reads the version of the jar on the class path from its manifest, with a
zip reader and inflater of its own (`zip.rs`, `inflate.rs`), and checks a master TLC's launch. It
declines TLC 1.7.4's jar and a manifest it can't read with certainty. Of the 117 CLI test runs, 56
now run natively; the rest decline at `-dump`, TLC 1.7.4 and the trace evaluator.

Since #250 the binary prints SANY's report of the trace exploration spec too, and checks TLC's
default natively. After an error trace of two states or more it writes the spec TLC writes,
`<Spec>_TTrace_<epoch>.tla`, and its path after `Finished in` (`te_spec.rs`), and for any
counterexample the trace file, `<Spec>_TTrace_<epoch>.bin`, which is identical where TLC reads it
back to the same trace (AGENTS.md, "The oracle"; cli.md, "-dumpTrace"). On the 733 corpus models in
TLC's default, against TLC's recordings of that mode, with each `.bin` compared by what the jar
reads back from it, 723 print and write what TLC does, 3 differ as they do with
`-noGenerateSpecTE`, by TLC's runtime (a Java stack overflow, where TLC is installed, and a
NullPointerException in TLC), and 7 decline at a trace file `tla-trace` doesn't dump: a random
draw, whose trace TLC may not find again for its postconditions (5), a set TLC keeps lazy (1), and a
deadlock that violates a temporal property (1).

### The public API afterwards

`check` and its option, progress, result and status types, `prove` and its types, `parseConfig`,
and the errors stay. `parseModule` and `Module` are the front end's to decide.

`Value`, `formatValue` and the values in `TraceStep` and `Violation` were the interpreter's
classes. The owner decided to break them, and they broke after the CLI's flip:

- `check` runs `checkSources` as the CLI does, with the spec and its configuration as the files
  `<Module>.tla` and `<Module>.cfg`, its modules through `loadModule`, and `-seed`, `-workers`,
  `-lncheck`, `-tool`, `-nowarning` and `-continue` from its options. The Json module's operators
  read and write the library's files there, through `readFile` (`read:<path>`) and `writeFile`
  (`Settings::json_files`): the engine reads what the library read for it before the search, and
  stops at a file it hasn't, which the library reads before the check runs again, so a check that
  reads a file only as it searches searches twice; it keeps what they write, which the library
  writes once the check ends, each file with what it was last written. The machine's `isLibrary`
  says so, and only then does the check write each printed state's plain
  data, at most 1,000,000 elements of it a variable, TLC's own bound on a set it builds; past
  that the value is `null`. The binary and the CLI's `checkSources` write none.
- The check records what it found as it prints (`prove-it-check`'s `outcome.rs`), and
  `checkSources` returns it as `outcome` (ABI 16): the status, the counts of TLC's statistics, what
  the spec printed, and each violation or error TLC reports, as its message's code and text with
  the states TLC prints after it. A state carries each variable as TLC prints it and as plain data.
- Where the native check stops before it searches, at a spec or configuration TLC rejects,
  `checkSources` returns the error the library throws for it as `thrown` (ABI 27), with what the
  spec printed before it, which the library prints first: a `TlaSyntaxError` with SANY's report
  (`createSanyError`), a `TlaConfigError` or a `TlaEvaluationError` with TLC's message, or a
  `TlaStackOverflowError`. Where the library can't know all TLC prints before the error,
  `checkSources` declines (see "Known wrong outputs"). Before ABI 27 `thrown` held only a
  `TlaConfigError` of tla-front's config error and a `TlaEvaluationError` for a temporal formula
  TLC can't check or a spec with no next-state action. SANY's report holds the errors of the
  first module with errors and the warnings so far, which the TypeScript check throws. The library
  left the error to the TypeScript check where the two may differ:
  - a fatal error of SANY's parsing phase, as the TypeScript check loads modules as it links them;
  - a module with a literal TLC can't hold, which the TypeScript check rejects as it loads it;
  - the arity of an instance's substitution, and a module defined twice, which it words its own
    way or doesn't report;
  - other evaluation errors, which it throws as its subclasses or not at all;
  - a stop after SANY or the spec printed, and a configuration or evaluation error in a spec that
    may print as TLC computes its constants (one that names `Print`, `PrintT`, TLCExt or IOUtils,
    or loads a Java override), which it prints first.
- Where the native check declines, stops before it searches without `thrown`, or the options ask
  for what only the TypeScript check does (`onPause`, a `dump` as `dot`, TLC 1.7.4), the
  TypeScript check runs and its result converts (`src/check-result.ts`). A `ModelConfig` goes to
  the native check as the configuration file that holds it (`formatConfig`), and a plain `dump` as
  `-dump`, whose file `checkSources` returns among its `writes` for `writeFile`.
  `systemProperties` go to the native check as a Java launch's `-D`, as the binary reads them.
- `Value` and `formatValue` are no longer exported.
- A set or function TLC keeps lazy is `{"@lazy": text}`, with TLC's `toString` of it, which the
  trace printer writes exactly as it writes the states (`tests/fixtures/plain-lazy` pins it against
  TLC's output). Where the text can't be TLC's, a value is `null`: a set TLC can't normalize
  natively, and in the interpreter a lazy function or filter it has no source for.
- `onPrint` gets what the spec printed once the native check ends, not as it prints. What the spec
  prints as TLC rebuilds a trace isn't in the result.

Of the 387 calls of the library's `check` in `bun run test` at the change, 199 ran natively. Of
the 188 others, 114 stopped before the search, 44 were declined and 30 asked for the TypeScript
check. The tests of the interpreter's own results run `checkParsed`, the TypeScript check. With
`thrown`, 104 of the 115 calls at 9cd662c6 that stop before the search throw the TypeScript check's
error natively, and 11 leave it to the TypeScript check.

### What changes for users

- `PROVE_IT_ENGINE=0` goes. Where no engine loads, `EngineUnavailableError` has no escape hatch:
  - WebAssembly fails to compile;
  - or `dist` lacks the engine.
  A browser keeps the WebAssembly engine.
- A WebAssembly stack overflow is an error, `WebAssemblyStackError`, in the library's check. The
  PR that removes `PROVE_IT_ENGINE=0` drops its message's clause that names it.
- `-dump`, `-continue` and periodic configs are checked natively. TLC 1.7.4's output is retired.
- The library prints what the binary prints. Today they differ only where the library hands over.

## Depth-first iterative deepening

The native CLI follows TLC's `-dfid` levels, fingerprint status bits and depth-first traversal for
single-worker searches. It reports TLC's level counts and depth-limit result. It declines a search
when TLC's independently seeded worker has more than one eligible state to choose, unless the
initial states have been verified to take one effect-free self-loop each, or when a DFID state fails
evaluation outside the supported single-action next-state and single-successor
invariant and implied-action failures. It prints invariant, action-property, and deadlock traces for pure,
unreduced states with `-noGenerateSpecTE`, directly from the worker's stack. It also reports
incomplete successors and their missing variables for those traces. It also declines coverage, dumps, `_POSSIBLE`, random draws, register writes, JSON files,
`TLCGet("distinct")`, `TLCGet("diameter")`, and effects in a
search generating multiple initial states or multiple successors. It reports TLC's constructor
errors for multiple workers and liveness before evaluating assumptions. It omits postcondition
checks, as DFID does. A tautology the frontend
rejects before it can determine DFID's liveness constructor error declines. `-continue` follows pure, unreduced runs with one generated initial state and no
ALIAS or trace files. Incomplete initial states are reported after TLC's batch generation;
initial-state evaluation failures decline except a single in-model initial state whose invariant
raises an EvalException and whose replay therefore skips it. Those guards leave traces and ordering whose exact output
is not yet followed to future work. The CLI handles invalid depth arguments as TLC does.

A failure that keeps TLC's call stack (of the next-state relation, an invariant or an action
property that fails to evaluate) is replayed on the next level, which prints the nested
expressions and counts the successor the replay generates again; at level `DFIDMax` the loop ends
before it (`DFIDModelChecker.modelCheckImpl`), so a failure at the last level prints neither
(`StopCounts::is_dfid_replayed`, `tests/dfid/last-*`). A recursion without end in the next-state
relation (as "A recursion without end" says the evaluator of failures proves) overflows TLC's
stack, which `doNext` catches as a `Throwable` and reports as `EC.SYSTEM_STACK_OVERFLOW` with the
trace to the state it was expanding; it keeps no call stack for it, so no replay prints nested
expressions or counts again, and TLC exits with 255. In a spec that prints or with temporal
properties it declines. The invariant and the action property `doNext` evaluates catch only an
`Exception`, so the same overflow there escapes to that `Throwable` too, with the successor in the
trace, where the search reported the invariant's or the property's evaluation failure (2111, on
the base too; main declined): it now declines ("a DFID violation or evaluation error"). Two more
shapes decline:
- "DFID of a spec without variables": the front end gives such a spec FALSE for Init and Next
  whether or not the configuration names a next-state relation, where TLC, with no action
  (`getActions().length == 0`), reports success right after the initial states, before any level;
- "-dfid with stacks TLC may not have the memory for": as each level starts, TLC's DFIDWorker
  allocates its stacks for every level up to -dfid (`TLCState[DFIDMax]`, `long[DFIDMax]`,
  `StateVec[DFIDMax]`, `LongVec[DFIDMax]` and a StateVec(1) and a LongVec(1) a level), over a
  hundred bytes a level: with 3 GB of heap the Jar runs out of memory at `-dfid 30000000` and
  `-dfid 2147483647`. A search that reaches level 2 with -dfid above 100,000 declines there: the
  relay cancels it as the level starts (`Relay::dfid_level`), so a spec that never ends, such as
  `Next == x' = x + 1`, declines at once and prints none of the levels after it.

## Options that change nothing TLC prints

`-gzip` and `-cleanup` change only the files TLC keeps under its meta directory; `-cleanup`
deletes the `states` directory where TLC runs, so the binary declines it where one is there
(`-cleanup with a states directory to delete`). `-fpmem` and `-fpbits` size the fingerprint set,
whose class only TLC's volatile banner names; TLC prints its deprecation notice of an absolute
`-fpmem` each time it reads such an option, and so does the binary. The binary declines a `-checkpoint`, `-fpbits` or `-coverage`
value, or a code of the lists below, with a character past ASCII, which `Integer.parseInt` may
read as a digit of another script (`Character.digit`), and `-fpmem` text that
isn't a plain decimal unless `Double.parseDouble` surely fails on it (no digit, neither NaN nor
Infinity), more than 8 `-fpbits` (where the Java heap decides whether TLC can allocate the
sets), an error after the notice, and the notice with several specs. `-checkpoint` reports TLC's
errors, with `Integer.parseInt(minutes) * 1000 * 60` overflowing as Java's ints do, and takes a
duration of zero, which turns checkpoints off; any other declines (`-checkpoint <minutes>`), since
TLC takes a checkpoint on a violation with states left (`ModelChecker.cleanup`).

`-suppressMessages` and `-messagesAsErrors` read their lists as `handleParameters` does:
`Integer.parseInt` of each trimmed item, whose exception TLC reports, a code outside EC's range, which holds EC.UNKNOWN, -1, and
no other negative code above UNIT_TEST (`unknown message code`), then `-nowarning` with codes to suppress and one code in both lists,
after the other options. The binary follows the codes TLC prints only through
`MP.printMessage`, `printState` or `printWarning`, which -suppressMessages silences (2149, 2190,
2191, 2193, 2194, 2199, 2217, 2268), and those it prints only through `printError`, which it
doesn't (2110, 2121, 2404); any other code of EC's declines (`-suppressMessages <code>`), as do
several codes in both lists. A code EC doesn't know is one of SANY's `ErrorCode`s
(`classifyMessageCode`): -suppressMessages rejects an error's at once ("code 4200 is an error and
cannot be suppressed."), and TLC rejects one SANY code in both lists by its name, after TLC's own
(`[EXTENDED_MODULES_SYMBOL_UNIFICATION_AMBIGUITY]`). The linter's warning,
RECORD_CONSTRUCTOR_FIELD_NAME_CLASH (4802), which SANY filters as it prints the linter's warnings
(`filterVisibleMessages`, `reportMessages`), is followed: suppressed, or printed as "Warning
treated as error: " after the others, which fails the parse. Any other of SANY's codes, which SANY
also filters among its parser's and its semantic analysis's warnings, whose codes the front end
doesn't keep, declines once the options are read ("SANY's message codes of -suppressMessages or
-messagesAsErrors"). A run declines where it prints a listed code otherwise
(`a message -suppressMessages names, printed as TLC may not silence`), and where it warns with a
code of -messagesAsErrors, which TLC turns into its failure
(`a warning -messagesAsErrors makes an error`), and -messagesAsErrors with -nowarning declines.

## -coverage in the engine

The engine's search doesn't count TLC's cost model; the replay pass in `tla-trace` does
(cli.md, "-coverage"). Counting in the engine was built (branch `engine-coverage`) and not adopted:
TLC with coverage runs 20 to 35 times as long as the engine's search on record-heavy specs, so the
times of TLC's report part way through can't be bounded from the engine's.

## tlapm

`prove-it tlapm …` runs natively (`prove-it-check`'s `tlapm.rs`): in the binary, and in the CLI of
`dist/`, which hands the command line to `checkSources` and applies the file operations its result
lists (`prove-it-host`'s `files.rs`). There is no TypeScript fallback: where the native command
declines, the CLI prints the decline and exits with 1, and where no engine loads, it throws
`EngineUnavailableError`. A run either prints and writes what tlapm does or declines as a whole:
both hold back what the run prints and writes until it ends (`prove-it-check`'s `overlay.rs`).

### What matches

- Every fixture tlapm 9ed0376 recorded in `tests/fixtures/obligations` and `tests/fixtures/tlapm-cli`
  (`prove-it-cli/tests/tlapm.rs`, `unit/cli.test.ts`): stdout, stderr and the exit status, with
  `-N`, `--toolbox`, `--line`, `--printallobs`, `--strict`, `--summary`, `--nofp`, `--cleanfp`, and
  over tlapm's own fingerprints file; the theory file byte for byte; and the fingerprints file,
  which holds what tlapm's holds but for each result's date and versions. tlapm copies Zenon's
  stderr to its stdout, and the native command writes Zenon's `exhausted search space` line, which
  the deleted TypeScript CLI left out. It sends Isabelle's stdout to a file (`Prep.isabelle_prove`), and
  Isabelle writes nothing to stderr for a proof it doesn't find, so such a failure prints as any
  other.
- `scripts/tlapm-conformance.ts` on the 1,873 modules of `tests/conformance/tlapm.json`, run as
  `record-tlapm.ts` ran tlapm (`-N --printallobs --toolbox 0 0`): every one of the 33,138
  obligations of the 1,507 modules tlapm accepted prints byte for byte, and the 366 modules it
  rejected decline.

### Upstream conformance

tla-ts, which Prove It was forked from, records tlapm b91fb6c and its backends on a suite of its
own (`packages/conformance/test/tlapm` of aidenybai/tla-ts, at 0341dbe5 of 2026-11-21): 1,351
tlapm command lines, run as `--strict --toolbox 0 0 --threads 1` with `-N --printallobs` or
`--debug tempfiles` by the test's mode, and 1,398 backend inputs each decided alone, 1,042 of them
SMT-LIB scripts from z3test recorded with Z3 5.3.2, which the SMT port declines as it reads only
what tlapm writes. Measured with a port of its harness (`scratch/upstream` on the
`upstream-results` branch): a run matches where its exit status and normalized transcript equal
the recording, declines where it prints `not native yet`, and is wrong otherwise. tlapm b91fb6c
is 20 commits past the 9ed0376 these fixtures record, which changed the time of HAVE, CASE, PICK
and USE facts and of a NEW bound, the arguments of declared non-constant operators and the typing
of integer powers; the runs those change count as wrong here until the port follows them.
One backend run, `backends/ls4/syntax/sometime_false`, carries tla-ts's correction of its
recording (unsat, the formula's meaning) and counts as wrong here, where Prove It answers sat as
`ptl_to_trp | ls4` does: ptl_to_trp prints the `False` of a renamed clause as a name, which LS4
reads as an atom.

| main | tlapm runs: match / decline / wrong | backend inputs: match / decline / wrong |
|---|---|---|
| b7f832b9 | 718 / 574 / 59 | 292 / 1,042 / 64 |
| with ptl_to_trp and LS4's reader | TLAPM_ROW | BACKEND_ROW |

### Declines

- **What timing decides** (`Schedule.run`): tlapm launches every decision it can, up to
  `--threads`, before it takes any result, and takes each as it comes back. Where two are in
  flight together, either can come back first, and the run declines where that changes what tlapm
  prints or writes: in toolbox mode, where each prints a message as it comes back (`toolbox
  messages of two decisions in flight at once, …`); a thunk still to be evaluated of an obligation
  with the fingerprint and prover of a decision in flight, which reuses its result or not as it
  comes back first or not; an SMT encoding still to be made that numbers CASE errors, whose count
  the order changes; Zenon's notes of different texts and Isabelle's proofs of different
  obligations, which tlapm writes as they come; and different results for one fingerprint and
  prover, of which the fingerprints file keeps the last. With one thread, or where one decision is
  in flight at a time, the order is tlapm's.
- **An error tlapm ends with** (`the backtrace tlapm prints as it ends with …`): tlapm prints the
  exception with the OCaml backtrace of where it raised it, and in toolbox mode a toolbox message of
  the location and message `Errors.set` kept (`tlapm_lib.ml`, `init`). Neither is known without a
  run of tlapm, and the recordings in `tests/fixtures/obligation-errors` leave the backtrace out. A
  module file that isn't there declines the same way. The deleted TypeScript CLI printed these without the
  backtrace.
- **What a back end writes that tlapm copies to its stdout.** tlapm runs each back end with its
  stderr on its own stdout (`System.launch_process`). Zenon's is known (`Zenon error: …`, from
  `prove.ml`'s `periodic` and `prove_fail`) and written. The native command declines:
  - a Zenon search that stops otherwise than on an exhausted search, the memory limit or the time
    limit, and an input a back end can't read.
- **What Prove It can't try as tlapm does:** a method with no back end in Prove It, and a method
  whose encoder can't take the obligation (`smt can't encode …`), where tlapm would try it. tlapm
  has no back end for Cooper either: it fails the method and warns `Cooper's method is not
  available any more.` on stderr (`Prep.prove_with`), which Prove It doesn't print yet. Where
  tlapm can't run cvc3, the error it prints holds the machine's PATH.
- **Command lines it doesn't model:** an option outside `src/cli/options.ts`'s list,
  `--printallobs` where tlapm proves (tlapm then prints each proved obligation's text too), an
  option without its arguments or without an integer (as OCaml's `int_of_string` reads one, with
  `0x`, `0o`, `0b` and `_`), a negative `--threads` (`Tlapm_args.set_max_threads` raises
  `Arg.Bad`, proving or not), `--threads` 0 or above 99 where tlapm proves (its scheduler
  asserts), and so a machine of more than 99 processors without `--threads`, no module, and
  globs. tlapm reports each in its own words, after a `--version` before it prints the version. An
  empty `-I`, and `-I +dir` where tlapm's standard library isn't found, end tlapm abnormally.
- **What `Loader` reads as tokens** (`what comes before the module header of …`): tlapm finds a
  module as `M_save.file_search'` does, in the current directory, each `-I` directory in the order
  given and its standard library, naming it by that path (`./M.tla`, `I1/M.tla`), or else through
  `Loader`, beside the command line's modules, naming it by its file's name alone. `Loader` hands
  the lexer the text, which it reads in token mode from the start rather than from the header on,
  so a module it reads with more than blanks and comments before its header declines.
- **A byte that isn't UTF-8 where the obligations hold it** (`a byte that isn't UTF-8 outside a
  comment in …`, naming the first module read that holds that byte): tlapm reads bytes, and read
  with U+FFFD for each such byte, two different strings would be one and a theorem that they are
  equal proved. Both the binary and the CLI read a module's bytes (`bytes:` keys) and decode them
  in `prove_obligations::bytes`: each byte that doesn't start a well-formed sequence (Unicode's
  Table 3-7) reads as a marker of its own, U+10FF00 plus the byte, the same for each byte value
  everywhere. The run declines where the obligations (everything they hold), a warning or an error
  hold a marker; elsewhere, as in a comment, before the module's header or past its end, it prints
  and proves what it would with U+FFFD. A module whose UTF-8 holds a character from U+10FF80 to
  U+10FFFF, which it would read alike with a byte, declines (`U+… in …, which Prove It reads a
  byte that isn't UTF-8 as`). Columns count bytes, as tlapm's do (`Loc`, `pos_cnum - pos_bol`),
  each marker one.
- **A cache it can't read or write as tlapm does:** a fingerprints file that doesn't load (tlapm
  moves it aside). Where tlapm can't make its cache directory or a module's in it
  (`Tlapm_lib.mkdir_tlaps`, a `Unix.mkdir`, which makes no directory above it), or write the
  fingerprints file, as where a directory is there, it ends abnormally with a backtrace (`the
  backtrace tlapm prints as it ends where it can't write …`). An empty cache directory, from
  `--cache-dir ""` or `TLAPM_CACHE_DIR=`, has tlapm make each module's directory at the root, which
  Prove It doesn't do. Where the file system refuses an operation the run's reads let it expect,
  as a directory under `/proc`, the binary and the CLI decline once the run ends (`a directory
  tlapm can't make: …`, `a file tlapm can't write: …`), with the operations before it applied.

### Declines to win back

Runs the deleted TypeScript CLI printed as tlapm does only by chance:
- A module named by an absolute Windows path, such as `C:\specs\M.tla`, which the port reads by
  tlapm's Unix rules and tlapm, which has no Windows build, never read (`a module named by an
  absolute Windows path, which tlapm reads only on Unix`). Winning it back takes a tlapm that runs
  on Windows to record.
- Toolbox mode with more than one thread, where two decisions are in flight together: the
  TypeScript printed each obligation's messages in order, which tlapm does only where the results
  happen to come back in that order.
- A method Prove It can't encode the obligation for (`smt can't encode …`) or has no back end for:
  the TypeScript left the method out, which printed what tlapm prints only where tlapm's attempt
  also failed and nothing printed it, as outside toolbox mode.
- A byte that isn't UTF-8 in a string the obligations hold but neither print nor prove, such as a
  theorem of a module the module extends: read as U+FFFD, the theorem was never read.

### Known wrong outputs

- `tlapm/test/fast/language/parse_function_comma_args.tla` #2: Prove It's SMT encoder writes the LET
  definitions inside the LET, and the SMT back end proves the obligation, where tlapm's
  `Smtlib.pp_print_expr` writes them outside it and Z3 rejects its input
  (`scripts/tlapm-deviations.ts`). tlapm reports a failure and Prove It a proof.
- An obligation a back end decides otherwise than tlapm's, within the same time limit, prints the
  other status. Run with `--threads 1 --toolbox 0 0` on the 248 modules of `proofs.json` with at
  most 120 obligations, against the statuses tlapm recorded there (measured 2026-11-12): 242 give
  every obligation tlapm's status, 5 decline (two `smt can't encode a temporal formula`, one `smt
  can't encode the operator Print`, cvc3 and Cooper), and 1 differs,
  `parse_function_comma_args.tla` #2 above. With more threads, a module where two decisions are in
  flight together declines in toolbox mode.
- A carriage return alone ends a `\*` comment for tlapm's lexer (`alexer.mll`'s `newline`), and
  not for the front end's, which reads the rest of the line as the comment.
- A TAB before the module header, on the header's line, shifts the columns printed on that line,
  because the front end expands tabs and tlapm counts bytes.
- tlapm writes each proof Zenon finds to the theory file (`Prep.save_result`, `Isabelle.thy_write`),
  with Zenon's input and the command it ran on a temporary file; Prove It's theory holds
  Isabelle's proofs alone.
- tlapm warns, on stderr or as a toolbox warning, where it reuses a proof found with a longer time
  limit than the method's (`Prep.already_processed`'s `success_warning`), which Prove It doesn't.
- tlapm prints `status:being proved` in toolbox mode for a decision that has run for `--wait`
  (3 s) (`Prep.mk_timec`), and stops launching others until then, which Prove It doesn't do.
- The toolbox header's command line is Prove It's, `prove-it tlapm …`, as tlapm prints its own
  (`tlapm_args.ml`, `init`); no recording holds tlapm's.
- The binary and the CLI of `dist/` print what the command printed once it ends, not as it goes.
  The binary keeps the order in which the run wrote to stdout and stderr; the CLI writes stdout,
  then stderr. Where both go to one file, neither need interleave them as tlapm, whose stdout is
  buffered, does.

Simulation executes the selected successor's last `TLCDefer` callback only when the linker
positively identifies the packaged TLCExt method under the modeled master/JDK 21 runtime and
closed resolver and override-index witnesses. BFS, ENABLED and unknown method origins retain
its earlier constant-TRUE compilation. Configuration tables and substitutions retain their own
resolution paths.

If a deferred body cannot compile, simulation discards the entire pure compilation and its
store, then compiles the model afresh with the earlier constant-TRUE treatment of every
`TLCDefer`, before startup or any runtime effects. This preserves matching discarded `JavaTime`
queries without inventing a clock value. Observable callbacks in such a model remain a known
difference: `TLCDefer(JavaTime) /\ TLCDefer(PrintT("chosen"))` still omits the print. Multiple
simulation workers remain unsupported.
