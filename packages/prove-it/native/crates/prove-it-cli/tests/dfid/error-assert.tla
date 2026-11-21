---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 0
Next == Assert(x > 0, "bad") /\ x' = x
====
