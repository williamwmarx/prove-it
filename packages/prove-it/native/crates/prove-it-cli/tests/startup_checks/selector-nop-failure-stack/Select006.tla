(*---
description: Actual selector failure.
outcome: any
flags: [expression]
---*)
---- MODULE Select006 ----
EXTENDS TLC,Naturals,Sequences
V==L::(1 \div 0)
Test==V!L=0
VARIABLE conformance_state
Init == conformance_state = Test
Next == UNCHANGED conformance_state
Inv == conformance_state
====
