(*---
description: ToTrace physical origin post_safe_eval_alias.
outcome: any
config: |
  INIT Init
  NEXT Next
  POSTCONDITION Post
---*)
---- MODULE Trace061 ----
EXTENDS TLCExt, TLC, Naturals, Sequences, FiniteSets
VARIABLE x
Init == x = 0
Next == UNCHANGED x
Inv == x = 0
Post == Len(ToTrace(TLCEval(CounterExample))) = 0
====
