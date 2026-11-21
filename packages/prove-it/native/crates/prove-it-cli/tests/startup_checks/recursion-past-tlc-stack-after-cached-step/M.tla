---- MODULE M ----
EXTENDS Integers, TLC
RECURSIVE G(_)
G(n) == IF n = 0 THEN 0 ELSE G(n - 1)
VARIABLE x
Init == x = 0
Next == (\A i \in 1..3 : G(1500) = 0) /\ G(4000) = 0 /\ x' = x
====
