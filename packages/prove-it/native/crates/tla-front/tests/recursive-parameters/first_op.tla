(*---
outcome: success
flags: [expression]
---*)
---- MODULE first_op ----
EXTENDS Integers
RECURSIVE R(_, _)
R(f(_), n) == IF n = 0 THEN 0 ELSE R(f, n-1)
Test == R(LAMBDA x : x, 2) = 0
====
