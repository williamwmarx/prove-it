(*---
outcome: success
flags: [expression]
---*)
---- MODULE last_op ----
EXTENDS Integers
RECURSIVE R(_, _)
R(n, f(_)) == IF n = 0 THEN 0 ELSE R(n-1, f)
Test == TRUE
====
