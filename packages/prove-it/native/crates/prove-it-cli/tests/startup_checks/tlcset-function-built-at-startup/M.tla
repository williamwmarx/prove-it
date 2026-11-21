---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Test == PrintT({y \in [i \in 1..2 |-> TLCSet(0, i)] : TRUE})
Init == x = 0
Next == x < 1 /\ x' = x + 1
ASSUME Test
====
