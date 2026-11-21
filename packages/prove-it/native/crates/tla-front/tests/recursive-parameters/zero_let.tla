(*---
outcome: success
flags: [expression]
---*)
---- MODULE zero_let ----
EXTENDS Integers
Test == LET RECURSIVE R
R == 0
IN R = 0
====
