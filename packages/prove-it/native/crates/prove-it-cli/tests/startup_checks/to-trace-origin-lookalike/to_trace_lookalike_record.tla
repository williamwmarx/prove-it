(*---
description: A record with the right fields is not a CounterExample.
ref: tlc2/module/TLCExt.java#lassoOrdinal
features:
  - TLCExt
flags:
  - expression
outcome: evaluation-failure
---*)
---- MODULE to_trace_lookalike_record ----
EXTENDS TLCExt, TLC, Naturals
Test == ToTrace([state |-> {}, action |-> {}]) = <<>>
ASSUME Test
====
