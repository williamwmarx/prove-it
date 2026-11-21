---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
Test == \E <<a, b>> \in (0..2147483647) \X {1} : TRUE
VARIABLE conformance_state
Init == conformance_state = Test
Next == UNCHANGED conformance_state
Inv == conformance_state
====
