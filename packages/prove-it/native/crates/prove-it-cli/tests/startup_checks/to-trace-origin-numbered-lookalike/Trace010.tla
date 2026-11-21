(*---
description: ToTrace physical origin numbered_states_direct.
outcome: any
flags: [expression]
---*)
---- MODULE Trace010 ----
EXTENDS TLCExt, TLC, Naturals, Sequences, FiniteSets
Test == ToTrace([state |-> {<<1,[x |-> 0]>>}, action |-> {}]) = <<>>
ASSUME Test
====
