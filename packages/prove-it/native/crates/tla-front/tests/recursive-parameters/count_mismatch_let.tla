(*---
outcome: success
flags: [expression]
---*)
---- MODULE count_mismatch_let ----
EXTENDS Integers
Test == LET RECURSIVE R(_)
R(f(_), n) == IF n = 0 THEN 0 ELSE R(f, n-1)
IN TRUE
====
