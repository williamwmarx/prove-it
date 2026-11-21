(*---
description: ToTrace physical origin function_strings_direct.
outcome: any
flags: [expression]
---*)
---- MODULE Trace016 ----
EXTENDS TLCExt, TLC, Naturals, Sequences, FiniteSets
Test == ToTrace([k \in {"state","action"} |-> {}]) = <<>>
ASSUME Test
====
