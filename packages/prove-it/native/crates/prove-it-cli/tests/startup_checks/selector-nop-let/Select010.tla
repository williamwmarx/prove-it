(*---
description: Actual selector let.
outcome: any
flags: [expression]
---*)
---- MODULE Select010 ----
EXTENDS TLC,Naturals,Sequences
Test==LET V==L::1 IN V!L=1
ASSUME Test
====
