(*---
description: With the fixed seed, the picks repeat exactly, printed normalized.
ref: tlc2/module/Randomization.java#RandomSetOfSubsets
features:
  - Randomization
flags:
  - expression
outcome: success
---*)
---- MODULE sos_seeded ----
EXTENDS Randomization, FiniteSets, Naturals, TLC
Test == PrintT(RandomSetOfSubsets(4, 2, 1..6))
VARIABLE conformance_state
Init == conformance_state=Test
Next == UNCHANGED conformance_state
Inv == conformance_state
====
