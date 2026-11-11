---- MODULE M ----
EXTENDS Naturals, TLC, Lib
VARIABLE x
Init == x = 0
Next == x' = x + 1 /\ Assert(x < 1, "x is one")
====
