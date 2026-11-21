---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
Test == (CHOOSE x \in 0..2147483647 : x = 0) = 0
VARIABLE conformance_state
Init == conformance_state = Test
Next == UNCHANGED conformance_state
Inv == conformance_state
====
