---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
Test == [{1} -> {x \in {y \in Nat : y > 1} : x > 3}] = [{1} -> {x \in {y \in Nat : y > 1} : x > 3}]
VARIABLE conformance_state
Init == conformance_state = Test
Next == UNCHANGED conformance_state
Inv == conformance_state
====
