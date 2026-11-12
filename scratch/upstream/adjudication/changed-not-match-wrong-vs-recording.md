# Changed runs where the candidate differs from the recording without declining

All four declined on the baseline; on the candidate each equals the pinned TLC jar byte for byte (exit and normalized transcript). The recording (older TLC) reports a SANY precedence-conflict parse error that the pinned jar no longer reports: a version gap, not a wrong output.

## tlc/generated/operators/domain/domain_cross#assume

```tla
---- MODULE domain_cross ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
Test == PrintT(DOMAIN {1, 2} \X {3})
====
```

Recorded exit 150. Pinned TLC exit 10, candidate exit 10, equal: True. Baseline: `prove-it: not native yet: an assumption that fails to evaluate: evaluating the assumption again: a startup definition that failed where TLC may fail otherwise: DOMAIN of a non-function`

```
2105:1 Evaluating assumption line 15, col 8 to line 15, col 11 of module domain_cross failed.
Attempted to apply the operator DOMAIN to a non-function
(a cartesian product)
line 14, col 16 to line 14, col 35 of module domain_cross
```

## tlc/generated/random/001/random_00581#assume

```tla
---- MODULE random_00581 ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
Test == PrintT([[[(CHOOSE r \in [a : 2..1] : TRUE) EXCEPT !.a = @ + (CHOOSE b980 \in Nat : TRUE)] EXCEPT !.a = @ + (Head(<<>>) * (1 % 2))] EXCEPT !.a = @ + ((CASE FALSE -> 7 [] OTHER -> 2 + IF FALSE THEN 3 ELSE 0) * (UNION {1..3, {2, 1, 3}} * [[a |-> 1] EXCEPT !.a = @ + TRUE]))])
====
```

Recorded exit 150. Pinned TLC exit 10, candidate exit 10, equal: True. Baseline: `prove-it: not native yet: an assumption that fails to evaluate: evaluating the assumption again: a startup definition that failed where TLC may fail otherwise: CHOOSE found no element`

```
2105:1 Evaluating assumption line 15, col 8 to line 15, col 11 of module random_00581 failed.
Attempted to compute the value of an expression of form
CHOOSE x \in S: P, but no element of S satisfied P.
line 14, col 20 to line 14, col 49 of module random_00581
```

## tlc/generated/random/005/random_02721#assume

```tla
---- MODULE random_02721 ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
Test == PrintT([(CHOOSE r \in [a : {}] : TRUE) EXCEPT !.a = @ + (-(UNION {{}, 2..1} * Head([x \in 1..2 |-> x])))])
====
```

Recorded exit 150. Pinned TLC exit 10, candidate exit 10, equal: True. Baseline: `prove-it: not native yet: an assumption that fails to evaluate: evaluating the assumption again: a startup definition that failed where TLC may fail otherwise: CHOOSE found no element`

```
2105:1 Evaluating assumption line 15, col 8 to line 15, col 11 of module random_02721 failed.
Attempted to compute the value of an expression of form
CHOOSE x \in S: P, but no element of S satisfied P.
line 14, col 18 to line 14, col 45 of module random_02721
```

## tlc/generated/random/016/random_08153#assume

```tla
---- MODULE random_08153 ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
Test == PrintT(SubSeq([SubSeq(SubSeq(<<3, 1, 2>>, SUBSET {1}, 2147483647), (SUBSET {1} - 1), Head(<<>>)) EXCEPT ![1] = ((TRUE + 2147483647) + Cardinality({}))], Cardinality(UNION {(CHOOSE r \in [a : {1, 2} \ {1}] : TRUE), (2147483647 .. 2)}), CASE (\E b12609 \in {-1 : b12610 \in {}} : ([a |-> 1] /\ FALSE)) -> (IF TRUE THEN 2 ELSE 2 \div Len(<<3, 1, 2>>)) [] OTHER -> LET b12611 == Len(<<1>>) IN Head(<<>>)))
====
```

Recorded exit 150. Pinned TLC exit 10, candidate exit 10, equal: True. Baseline: `prove-it: not native yet: an assumption that fails to evaluate: evaluating the assumption again: a startup definition that failed where TLC may fail otherwise: SubSeq of a bound that isn't an integer`

```
2105:1 Evaluating assumption line 15, col 8 to line 15, col 11 of module random_08153 failed.
2169:0 The second argument of SubSeq should be a natural number, but instead it is:
{{}, {1}}
```

