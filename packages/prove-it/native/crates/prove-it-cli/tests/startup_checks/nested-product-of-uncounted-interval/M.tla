---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
Test == \E x \in ((0..2147483647) \X {1}) \X {2} : TRUE
VARIABLE conformance_state
Init == conformance_state = TRUE
Next == conformance_state' = Test
Inv == conformance_state
====
