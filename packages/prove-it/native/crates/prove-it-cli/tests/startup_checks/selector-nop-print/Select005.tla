(*---
description: Actual selector effect.
outcome: any
flags: [expression]
---*)
---- MODULE Select005 ----
EXTENDS TLC,Naturals,Sequences
V==L::PrintT(1)
Test==V!L
ASSUME Test
====
