(*---
outcome: success
flags: [expression]
---*)
---- MODULE one_op ----
EXTENDS Integers
RECURSIVE R(_)
R(f(_)) == 0
Test == TRUE
====
