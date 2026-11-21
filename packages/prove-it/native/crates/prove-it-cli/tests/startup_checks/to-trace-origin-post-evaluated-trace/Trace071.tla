(*---
description: ToTrace physical origin post_violation_eval_alias.
outcome: any
config: |
  INIT Init
  NEXT Next
  POSTCONDITION Post
  INVARIANT Inv
---*)
---- MODULE Trace071 ----
EXTENDS TLCExt, TLC, Naturals, Sequences, FiniteSets
VARIABLE x
Init == x = 0
Next == x' = 1
Inv == x = 0
Post == Len(ToTrace(TLCEval(CounterExample))) = 2
====
