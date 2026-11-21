---- MODULE M ----
EXTENDS Integers, FiniteSets
VARIABLE x
Test == [<<1, 2>> EXCEPT ![1] = Cardinality(Nat)][2] = 2
Init == x = 0 /\ Test
Next == x' = x
====
