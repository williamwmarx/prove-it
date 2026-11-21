---- MODULE M ----
EXTENDS Integers, TLC
RECURSIVE G(_)
G(n) == IF n = 0 THEN 0 ELSE G(n - 1)
ASSUME G(6500) = 0
====
