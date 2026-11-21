(*---
description: ToTrace post_safe_missing_except_alias.
outcome: any
config: |
  INIT Init
  NEXT Next
  POSTCONDITION Post
args: ["-nowarning"]
---*)
---- MODULE Extra002 ----
EXTENDS TLCExt, TLC, Naturals, Sequences
VARIABLE x
Init == x = 0
Next == UNCHANGED x
Inv == x = 0
Post == Len(ToTrace([CounterExample EXCEPT !.missing = 42])) = 0
====
