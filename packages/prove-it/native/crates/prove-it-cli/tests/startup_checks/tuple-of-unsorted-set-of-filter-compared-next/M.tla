---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
Test == <<{{x \in Nat : x > 1}, {}}>> = <<{}>>
VARIABLE conformance_state
Init == conformance_state = TRUE
Next == conformance_state' = Test
Inv == conformance_state
====
