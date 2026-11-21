(*---
outcome: success
flags: [expression]
---*)
---- MODULE let_forward ----
EXTENDS Integers
Test == LET RECURSIVE R(_, _)
Forward(g(_), n) == g(n)
R(f(_), n) == IF n = 0 THEN Forward(f, 1) ELSE R(f, n-1)
IN R(LAMBDA x : x+1, 2) = 2
====
