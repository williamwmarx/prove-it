(*---
description: ToTrace physical origin local_shadow.
outcome: any
flags: [expression]
---*)
---- MODULE Trace052 ----
EXTENDS TLCExt, TLC, Naturals, Sequences, FiniteSets
Test == LET ToTrace(v) == TRUE IN ToTrace([state |-> {}, action |-> {}])
ASSUME Test
====
