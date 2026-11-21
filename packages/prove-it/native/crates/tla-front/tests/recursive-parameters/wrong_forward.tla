(*---
outcome: success
flags: [expression]
---*)
---- MODULE wrong_forward ----
EXTENDS Integers
RECURSIVE R(_, _)
R(f(_, _), n) == IF n = 0 THEN f(1,2) ELSE R(LAMBDA x : x, n-1)
Test == TRUE
====
