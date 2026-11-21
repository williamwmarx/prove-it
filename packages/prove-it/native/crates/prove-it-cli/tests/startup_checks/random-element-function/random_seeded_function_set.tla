(*---
description: With the fixed seed, the picks from a function set repeat exactly.
ref: tlc2/module/TLC.java#RandomElement
features:
  - TLC
flags:
  - expression
outcome: success
---*)
---- MODULE random_seeded_function_set ----
EXTENDS TLC, Naturals
Test == PrintT(RandomElement([1..5 -> 1..100]))
VARIABLE conformance_state
Init == conformance_state=Test
Next == UNCHANGED conformance_state
Inv == conformance_state
====
