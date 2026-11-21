(*---
description: S must not be Nat.
ref: tlc2/module/Randomization.java#RandomSetOfSubsets
features:
  - Randomization
flags:
  - expression
outcome: evaluation-failure
---*)
---- MODULE sos_third_nat ----
EXTENDS Randomization, FiniteSets, Naturals
Test == RandomSetOfSubsets(1, 1, Nat) = {}
ASSUME Test
====
