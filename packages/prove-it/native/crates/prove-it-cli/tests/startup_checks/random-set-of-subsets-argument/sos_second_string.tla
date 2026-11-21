(*---
description: n must be an integer.
ref: tlc2/module/Randomization.java#RandomSetOfSubsets
features:
  - Randomization
flags:
  - expression
outcome: evaluation-failure
---*)
---- MODULE sos_second_string ----
EXTENDS Randomization, FiniteSets, Naturals
Test == RandomSetOfSubsets(1, "a", {1}) = {}
VARIABLE conformance_state
Init == conformance_state=Test
Next == UNCHANGED conformance_state
Inv == conformance_state
====
