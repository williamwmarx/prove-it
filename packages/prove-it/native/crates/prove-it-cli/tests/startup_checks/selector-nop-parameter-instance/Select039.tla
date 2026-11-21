(*---
description: Actual selector instance_parameter.
outcome: any
flags: [expression]
includes: ["Lib.tla"]
---*)
---- MODULE Select039 ----
EXTENDS TLC,Naturals,Sequences
I==INSTANCE Lib WITH c<-1
Test==I!P(2)!L=2
ASSUME Test
====
