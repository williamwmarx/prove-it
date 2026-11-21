---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
VARIABLE cs
Test == (CHOOSE b \in ([a |-> 1] \ (Int \X {"a", 1})) : TRUE) = 1
ASSUME Test
Init == cs = 0
Next == cs' = cs
====
