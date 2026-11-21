(*---
description: Actual selector instance.
outcome: any
flags: [expression]
includes: ["Lib.tla"]
---*)
---- MODULE Select038 ----
EXTENDS TLC,Naturals,Sequences
I==INSTANCE Lib WITH c<-1
Test==I!V!L=1
ASSUME Test
====
