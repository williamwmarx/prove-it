(*---
description: ToTrace physical origin post_safe_direct.
outcome: any
config: |
  INIT Init
  NEXT Next
  POSTCONDITION Post
---*)
---- MODULE Trace057 ----
EXTENDS TLCExt, TLC, Naturals, Sequences, FiniteSets
VARIABLE x
Init == x = 0
Next == UNCHANGED x
Inv == x = 0
Post == Len(ToTrace(CounterExample)) = 0
====
