(*---
description: ToTrace physical origin mixed_set_direct.
outcome: any
flags: [expression]
---*)
---- MODULE Trace028 ----
EXTENDS TLCExt, TLC, Naturals, Sequences, FiniteSets
Test == ToTrace({1,"a"}) = <<>>
ASSUME Test
====
