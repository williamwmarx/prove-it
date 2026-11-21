---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC, Randomization
Test == TLCSet(Nat, TLCSet(1, 2))
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
Inv == x < 1 \/ Test
====
