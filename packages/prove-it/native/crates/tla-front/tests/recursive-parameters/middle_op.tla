(*---
outcome: success
flags: [expression]
---*)
---- MODULE middle_op ----
EXTENDS Integers
RECURSIVE R(_, _, _)
R(a, f(_), n) == IF n = 0 THEN f(a) ELSE R(a, f, n-1)
Test == R(4, LAMBDA x : x+1, 2) = 5
====
