(*---
description: ToTrace physical origin action_only_direct.
outcome: any
flags: [expression]
---*)
---- MODULE Trace006 ----
EXTENDS TLCExt, TLC, Naturals, Sequences, FiniteSets
Test == ToTrace([action |-> {}]) = <<>>
ASSUME Test
====
