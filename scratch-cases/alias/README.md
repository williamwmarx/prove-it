# ALIAS review cases (data only, not for merging)

Adversarial inputs from the review rounds of two branches, for the design of which definitions TLC
computes as it starts. Each archive unpacks to one directory per round. Each case is a directory
with `M.tla`, `M.cfg` and any other modules it reads; the round's generators (`*.py`) and its
result files sit beside the cases.

Each result line gives, for main and for the branch, the outcome against TLC at d8fb231 at
-workers 1 and 4, plain and -tool:

- `SAME`: byte-identical output;
- `DECLINE`: the binary said `not native yet`, with the reason;
- `DIFF(tlc exit/native exit)`: different output, with the first lines of the diff.

At -workers 4, a DIFF in only "The depth of the complete state graph" or "The average outdegree"
is TLC's own nondeterminism.

## constant-alias (#328)

Literal, cfg-assigned and substituted ALIAS and POSTCONDITION definitions (`Definition::LITERAL`).

- `breakC.tar.gz` … `breakC6.tar.gz`: rounds 1 to 6. Results are in `out*.txt`, or for round 1 in
  `rerun.out`. Rounds 2 to 6 hold multi-module cases, run with `breakC2/case3N.sh`.
- `constant-alias-rerun.txt`: every case of the six rounds rerun on the branch at 7d727d5b against
  main 9cd662c6. Each entry is a case name, then its main line, then its branch line.

## alias-trace-fixes (dropped, see fallback.md "Known wrong outputs")

Lazy recursive function definitions in an ALIAS, sets TLC can't normalize, `\cup` of unnormalized
sets, and ALIAS states TLC fingerprints.

- `break1.tar.gz` … `break3.tar.gz`: rounds 1 to 3. Cases are under `c/`, results in `b*.out` or
  `p*.out`. The "main" there is 40009ac8.
- `alias-trace-fixes-rerun.txt`: rounds 1 and 2 rerun on the branch with its two-pass ALIAS
  evaluation. Round 3 found that design still leaks: `UNION` and `\` of a set holding a lazy
  function, `IsFiniteSet`, `\X` and record sets over it.
