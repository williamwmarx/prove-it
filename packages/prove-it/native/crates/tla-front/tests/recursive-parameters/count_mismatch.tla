(*---
outcome: success
flags: [expression]
---*)
---- MODULE count_mismatch ----
EXTENDS Integers
RECURSIVE R(_)
R(f(_), n) == IF n = 0 THEN 0 ELSE R(f, n-1)
Test == TRUE
====
