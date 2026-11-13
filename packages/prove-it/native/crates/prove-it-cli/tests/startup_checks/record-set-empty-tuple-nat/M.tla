---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Init == x = (<<>> \in [a : Nat])
Next == x' = x
====
