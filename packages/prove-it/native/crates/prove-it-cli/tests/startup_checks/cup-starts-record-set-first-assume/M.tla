---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
VARIABLE cs
Test == PrintT([a : ([a : (0 = 7)] \cup UNION [a : {1}])])
ASSUME Test
Init == cs = 0
Next == cs' = cs
====
