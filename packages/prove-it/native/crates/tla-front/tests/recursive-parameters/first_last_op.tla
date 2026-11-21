(*---
outcome: success
flags: [expression]
---*)
---- MODULE first_last_op ----
EXTENDS Integers
RECURSIVE R(_, _, _)
R(f(_), n, g(_)) == IF n = 0 THEN f(1) ELSE R(f, n-1, g)
Test == TRUE
====
