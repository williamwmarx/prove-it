(*---
description: ToTrace physical origin post_safe_except_copy.
outcome: any
config: |
  INIT Init
  NEXT Next
  POSTCONDITION Post
---*)
---- MODULE Trace063 ----
EXTENDS TLCExt, TLC, Naturals, Sequences, FiniteSets
VARIABLE x
Init == x = 0
Next == UNCHANGED x
Inv == x = 0
Post == Len(ToTrace([CounterExample EXCEPT !.state = @])) = 0
====
