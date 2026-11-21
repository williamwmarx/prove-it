---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
Test == SUBSET {x \in Int : x > 3} = SUBSET {x \in Int : x > 3}
VARIABLE conformance_state
Init == conformance_state = TRUE
Next == conformance_state' = Test
Inv == conformance_state
====
