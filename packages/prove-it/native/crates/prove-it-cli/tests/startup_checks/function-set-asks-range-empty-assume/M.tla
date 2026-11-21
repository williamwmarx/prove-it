---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
VARIABLE cs
Test == \E s \in SUBSET [DOMAIN [x \in Nat |-> x + 1] -> 1] : TRUE
ASSUME Test
Init == cs = 0
Next == cs' = cs
====
