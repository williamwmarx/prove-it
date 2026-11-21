(*---
description: ToTrace post_safe_equal_alias.
outcome: any
config: |
  INIT Init
  NEXT Next
  POSTCONDITION Post
---*)
---- MODULE Extra000 ----
EXTENDS TLCExt, TLC, Naturals, Sequences
VARIABLE x
Init == x = 0
Next == UNCHANGED x
Inv == x = 0
Post == LET c == CounterExample IN c = [state |-> c.state, action |-> c.action] /\ Len(ToTrace(c)) = 0
====
