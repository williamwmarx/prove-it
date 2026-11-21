---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
F[n \in 1..2] == IF PrintT(n) /\ n = 1 THEN 1 ELSE F[n - 1]
Test == F[2] = 1 /\ F[2] = 1
ASSUME Test
Init == x = 0
Next == x' = x
====
