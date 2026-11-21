(*---
outcome: success
flags: [expression]
---*)
---- MODULE arity2_let ----
EXTENDS Integers
Test == LET RECURSIVE R(_, _)
R(f(_, _), n) == IF n = 0 THEN f(1, 2) ELSE R(f, n-1)
IN R(LAMBDA x, y : x+y, 2) = 3
====
