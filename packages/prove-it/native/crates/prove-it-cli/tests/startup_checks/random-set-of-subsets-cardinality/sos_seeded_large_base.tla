(*---
description: A base set larger than 31 elements stays in the first exponent check's shortcut.
ref: tlc2/module/Randomization.java#RandomSetOfSubsets
features:
  - Randomization
flags:
  - expression
outcome: success
---*)
---- MODULE sos_seeded_large_base ----
EXTENDS Randomization, FiniteSets, Naturals, TLC
Test == PrintT(Cardinality(RandomSetOfSubsets(3, 16, 1..32)))
VARIABLE conformance_state
Init == conformance_state=Test
Next == UNCHANGED conformance_state
Inv == conformance_state
====
