(*---
description: ToTrace post_safe_register_alias.
outcome: any
config: |
  INIT Init
  NEXT Next
  POSTCONDITION Post
---*)
---- MODULE Extra003 ----
EXTENDS TLCExt, TLC, Naturals, Sequences
VARIABLE x
Init == x = 0
Next == UNCHANGED x
Inv == x = 0
Post == TLCSet(1,CounterExample) /\ Len(ToTrace(TLCGet(1))) = 0
====
