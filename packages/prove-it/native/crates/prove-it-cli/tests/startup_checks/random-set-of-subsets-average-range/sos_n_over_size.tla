(*---
description: n > |S| is rejected with its range.
ref: tlc2/module/Randomization.java#RandomSetOfSubsets
features:
  - Randomization
flags:
  - expression
outcome: evaluation-failure
---*)
---- MODULE sos_n_over_size ----
EXTENDS Randomization, FiniteSets, Naturals
Test == RandomSetOfSubsets(1, 3, {1, 2}) = {}
VARIABLE conformance_state
Init == conformance_state=TRUE
Next == UNCHANGED conformance_state
Inv == conformance_state /\ Test
====
