(*---
outcome: success
flags: [expression]
---*)
---- MODULE one_op_let ----
EXTENDS Integers
Test == LET RECURSIVE R(_)
R(f(_)) == 0
IN TRUE
====
