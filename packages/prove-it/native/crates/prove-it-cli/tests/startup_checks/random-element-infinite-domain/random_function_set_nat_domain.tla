(*---
description: A function set over Nat cannot enumerate its domain.
ref: tlc2/module/TLC.java#RandomElement
features:
  - TLC
flags:
  - expression
outcome: evaluation-failure
---*)
---- MODULE random_function_set_nat_domain ----
EXTENDS TLC, Naturals
Test == RandomElement([Nat -> {1}]) = 0
VARIABLE conformance_state
Init == conformance_state=TRUE
Next == conformance_state'=Test
Inv == conformance_state
====
