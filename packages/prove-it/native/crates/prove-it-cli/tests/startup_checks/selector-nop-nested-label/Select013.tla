(*---
description: Actual selector nested_labels.
outcome: any
flags: [expression]
---*)
---- MODULE Select013 ----
EXTENDS TLC,Naturals,Sequences
V==L::(M::1)
Test==V!L!M=1
ASSUME Test
====
