---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
Test == [{<<1>>} -> {x \in Nat : x > 3}] = [{<<1>>} -> {x \in Nat : x > 3}]
VARIABLE conformance_state
Init == conformance_state = TRUE
Next == conformance_state' = Test
Inv == conformance_state
====
