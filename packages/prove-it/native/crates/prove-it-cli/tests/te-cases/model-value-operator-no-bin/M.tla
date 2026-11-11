---- MODULE M ----
EXTENDS Naturals, TLC
CONSTANTS Procs
VARIABLE x
Init == x = 0
Next == x' = x + 1 /\ Assert(x < 1, "bad")
====
