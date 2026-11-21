---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
VARIABLE cs
Test == (CHOOSE b \in (DOMAIN (0 :> 2) \cup (([x \in Nat |-> x + 1] :> 2) \cap UNION {{2, 1, 3}, SUBSET {1}})) : TRUE) = 0
ASSUME Test
Init == cs = 0
Next == cs' = cs
====
