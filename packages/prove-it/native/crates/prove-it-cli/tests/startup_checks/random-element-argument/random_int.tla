(*---
description: A non-set says a finite set was expected.
ref: tlc2/module/TLC.java#RandomElement
features:
  - TLC
flags:
  - expression
outcome: evaluation-failure
---*)
---- MODULE random_int ----
EXTENDS TLC, Naturals
Test == RandomElement(3) = 0
VARIABLE conformance_state
Init == conformance_state=Test
Next == UNCHANGED conformance_state
Inv == conformance_state
====
