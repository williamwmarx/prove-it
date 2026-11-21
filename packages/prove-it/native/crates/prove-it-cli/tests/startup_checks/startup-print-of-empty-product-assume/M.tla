---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
VARIABLE cs
Test == PrintT({} \X SetToBag({1}))
ASSUME Test
Init == cs = 0
Next == cs' = cs
====
