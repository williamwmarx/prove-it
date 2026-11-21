(*---
outcome: success
flags: [expression]
---*)
---- MODULE forward ----
EXTENDS Integers
RECURSIVE R(_, _)
Forward(g(_), n) == g(n)
R(f(_), n) == IF n = 0 THEN Forward(f, 1) ELSE R(f, n-1)
Test == R(LAMBDA x : x+1, 2) = 2
====
