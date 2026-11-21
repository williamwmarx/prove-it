---- MODULE M ----
EXTENDS Integers, TLC
RECURSIVE Twice(_, _)
Twice(f(_), n) == IF n = 0 THEN f(0) ELSE Twice(LAMBDA y : f(y) + 1, n - 1)
ASSUME Twice(LAMBDA y : y, 2) = 2
====
