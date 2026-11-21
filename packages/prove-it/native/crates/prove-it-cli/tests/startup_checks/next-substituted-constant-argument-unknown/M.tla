---- MODULE M ----
EXTENDS Naturals, TLC, Randomization, Sequences
VARIABLE x
CONSTANT C(_)
Init == x = 0
Op(a) == x' = 1
Next == C(<<1>>[2])
====
