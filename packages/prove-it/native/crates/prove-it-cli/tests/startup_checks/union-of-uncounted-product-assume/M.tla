---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
Test == \E x \in UNION {(0..2147483647) \X {1}} : TRUE
VARIABLE cs
ASSUME Test
Init == cs = 0
Next == cs' = cs
====
