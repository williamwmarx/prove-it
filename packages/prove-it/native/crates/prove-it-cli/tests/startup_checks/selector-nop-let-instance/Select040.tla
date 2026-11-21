(*---
description: Actual selector instance_let.
outcome: any
flags: [expression]
includes: ["Lib.tla"]
---*)
---- MODULE Select040 ----
EXTENDS TLC,Naturals,Sequences
Test==LET I==INSTANCE Lib WITH c<-1 IN I!V!L=1
ASSUME Test
====
