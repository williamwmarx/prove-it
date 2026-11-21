---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
F[n \in 1..2] == IF PrintT(n) /\ n = 1 THEN 1 ELSE F[n - 1]
Init == x = F[2]
Next == x' = x
====
