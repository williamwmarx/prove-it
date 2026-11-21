(*---
description: ToTrace physical origin operator_alias_record.
outcome: any
flags: [expression]
---*)
---- MODULE Trace049 ----
EXTENDS TLCExt, TLC, Naturals, Sequences, FiniteSets
Id(v) == v
Test == ToTrace(Id([state |-> {}, action |-> {}])) = <<>>
ASSUME Test
====
