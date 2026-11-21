---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
Test == [{1} -> {x \in Nat : x > 3}] = {}
VARIABLE conformance_state
Init == conformance_state = Test
Next == UNCHANGED conformance_state
Inv == conformance_state
====
