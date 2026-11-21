(*---
outcome: success
flags: [expression]
---*)
---- MODULE plain ----
EXTENDS Integers
RECURSIVE R(_, _)
R(a, n) == IF n = 0 THEN a ELSE R(a, n-1)
Test == R(4, 2) = 4
====
