---- MODULE M ----
EXTENDS Naturals, TLC, Randomization, Sequences
VARIABLE x
CONSTANT C(_)
Init == x = 0
Op(a) == x' = (x + 1) % 3
Next == C(RandomElement({1, 2}))
K == RandomElement(1..30)
ASSUME PrintT(K)
====
