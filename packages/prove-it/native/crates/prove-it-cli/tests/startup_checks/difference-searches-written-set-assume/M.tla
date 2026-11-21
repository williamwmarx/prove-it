---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
VARIABLE cs
Test == {x : x \in ({1} \X {2} \X {{}, {1}}) \ {1, 2}} = {}
ASSUME Test
Init == cs = 0
Next == cs' = cs
====
