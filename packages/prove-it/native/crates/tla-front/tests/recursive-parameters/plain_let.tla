(*---
outcome: success
flags: [expression]
---*)
---- MODULE plain_let ----
EXTENDS Integers
Test == LET RECURSIVE R(_, _)
R(a, n) == IF n = 0 THEN a ELSE R(a, n-1)
IN R(4, 2) = 4
====
