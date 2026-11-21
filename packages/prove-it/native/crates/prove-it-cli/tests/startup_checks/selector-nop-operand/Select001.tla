(*---
description: Actual selector operand.
outcome: any
flags: [expression]
---*)
---- MODULE Select001 ----
EXTENDS TLC,Naturals,Sequences
V==1+2
Test==V!1=1
ASSUME Test
====
