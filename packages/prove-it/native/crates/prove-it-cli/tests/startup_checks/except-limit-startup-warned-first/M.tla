---- MODULE M ----
EXTENDS Integers, FiniteSets
VARIABLE x
Test == [<<1, 2>> EXCEPT ![3] = 1, ![1] = Cardinality(Nat)][2] = 2
ASSUME Test
Init == x = 0
Next == x' = x
====
