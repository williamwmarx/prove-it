(*---
description: Actual selector constant.
outcome: any
flags: [expression]
---*)
---- MODULE Select000 ----
EXTENDS TLC,Naturals,Sequences
V==L::1
Test==V!L=1
ASSUME Test
====
