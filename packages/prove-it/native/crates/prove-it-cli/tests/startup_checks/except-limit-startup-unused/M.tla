---- MODULE M ----
EXTENDS Integers, FiniteSets, Sequences
VARIABLE x
Test == [<<1, 2>> EXCEPT ![1] = Len(Nat)][2] = 2
Init == x = 0
Next == x' = x
====
