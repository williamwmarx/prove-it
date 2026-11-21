(*---
description: Actual selector parameter.
outcome: any
flags: [expression]
---*)
---- MODULE Select008 ----
EXTENDS TLC,Naturals,Sequences
V(p)==L::p
Test==V(1)!L=1
ASSUME Test
====
