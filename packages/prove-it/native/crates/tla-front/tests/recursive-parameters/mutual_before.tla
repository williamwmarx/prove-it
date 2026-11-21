(*---
outcome: success
flags: [expression]
---*)
---- MODULE mutual_before ----
EXTENDS Integers
RECURSIVE R(_, _), S(_, _)
R(f(_), n) == IF n = 0 THEN f(1) ELSE S(f, n-1)
S(g(_), n) == IF n = 0 THEN g(1) ELSE R(g, n-1)
Test == TRUE
====
