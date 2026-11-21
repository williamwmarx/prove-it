(*---
description: A non-string probability asks for a string literal.
ref: tlc2/module/Randomization.java#RandomSubsetSet
features:
  - Randomization
flags:
  - expression
outcome: evaluation-failure
includes:
  - Randomization.tla
---*)
---- MODULE sss_second_non_string ----
EXTENDS Randomization, FiniteSets, Naturals
Test == RandomSubsetSet(1, 1, {1}) = {}
VARIABLE conformance_state
Init == conformance_state=TRUE
Next == UNCHANGED conformance_state
Inv == conformance_state /\ Test
====
