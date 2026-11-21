(*---
outcome: success
flags: [expression]
---*)
---- MODULE local ----
EXTENDS Integers
RECURSIVE R(_, _)
LOCAL R(f(_), n) == IF n = 0 THEN f(1) ELSE R(f, n-1)
Test == R(LAMBDA x : x+1, 2) = 2
====
