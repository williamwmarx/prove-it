---- MODULE M ----
EXTENDS Naturals, TLC, Randomization, Sequences
VARIABLE x
CONSTANT C(_)
Init == x = 0
Op(a) == x' = (x + 1) % 3
Next == C(RandomElement({1, 2})) \/ C(RandomElement(1..4)) \/ C(RandomSubset(1, {}))
ASSUME RandomElement({3}) = 3
====
