---- MODULE M ----
EXTENDS Integers, TLC
RECURSIVE G(_)
G(n) == IF n = 0 THEN 0 ELSE G(n - 1)
ASSUME \A i \in 1..3 : G(1500) = 0
ASSUME G(6500) = 0
====
