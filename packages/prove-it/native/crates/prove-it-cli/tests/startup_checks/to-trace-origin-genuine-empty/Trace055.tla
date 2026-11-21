(*---
description: ToTrace physical origin builtin_counterexample.
outcome: any
flags: [expression]
---*)
---- MODULE Trace055 ----
EXTENDS TLCExt, TLC, Naturals, Sequences, FiniteSets
Test == ToTrace(CounterExample) = <<>>
ASSUME Test
====
