(*---
description: k > 2^|S| is rejected, naming the size.
ref: tlc2/module/Randomization.java#RandomSubsetSet
features:
  - Randomization
flags:
  - expression
outcome: evaluation-failure
includes:
  - Randomization.tla
---*)
---- MODULE sss_k_over_max ----
EXTENDS Randomization, FiniteSets, Naturals
Test == RandomSubsetSet(5, "0.5", {1, 2}) = {}
VARIABLE conformance_state
Init == conformance_state=TRUE
Next == conformance_state'=Test
Inv == conformance_state
====
