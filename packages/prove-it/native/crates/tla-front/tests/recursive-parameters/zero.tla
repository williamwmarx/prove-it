(*---
outcome: success
flags: [expression]
---*)
---- MODULE zero ----
EXTENDS Integers
RECURSIVE R
R == 0
Test == R = 0
====
