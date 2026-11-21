(*---
description: The k bound is checked before the n range.
ref: tlc2/module/Randomization.java#RandomSetOfSubsets
features:
  - Randomization
flags:
  - expression
outcome: evaluation-failure
---*)
---- MODULE sos_check_order_k_before_n ----
EXTENDS Randomization, FiniteSets, Naturals
Test == RandomSetOfSubsets(5, 3, {1, 2}) = {}
VARIABLE conformance_state
Init == conformance_state=TRUE
Next == conformance_state'=Test
Inv == conformance_state
====
