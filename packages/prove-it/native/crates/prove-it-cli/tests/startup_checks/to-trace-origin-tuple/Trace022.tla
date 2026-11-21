(*---
description: ToTrace physical origin tuple_direct.
outcome: any
flags: [expression]
---*)
---- MODULE Trace022 ----
EXTENDS TLCExt, TLC, Naturals, Sequences, FiniteSets
Test == ToTrace(<<1,2>>) = <<>>
ASSUME Test
====
