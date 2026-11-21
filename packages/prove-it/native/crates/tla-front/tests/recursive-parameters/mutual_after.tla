(*---
outcome: success
flags: [expression]
---*)
---- MODULE mutual_after ----
EXTENDS Integers
RECURSIVE R(_, _), S(_, _)
R(f(_), n) == IF n = 0 THEN f(1) ELSE R(f, n-1)
S(g(_), n) == IF n = 0 THEN g(1) ELSE R(g, n-1)
Test == S(LAMBDA x : x+1, 2) = 2
====
