---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
CONSTANT C(_)
Init == x = 0
Op(a) == x' = (x + 1) % 3
Next == C(RandomElement({1, 2, 3, 4, 5, 6, 7, 8}))
====
