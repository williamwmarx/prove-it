---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC, Randomization
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
Test == TLCSet([a |-> 1], 1)
Inv == x < 1 \/ Test
====
