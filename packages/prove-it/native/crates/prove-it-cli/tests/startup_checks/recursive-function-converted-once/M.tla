---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
F[n \in 0..2] == IF PrintT(n) /\ n = 0 THEN 0 ELSE F[n - 1] + F[n - 1]
Test == F[2] = 0 /\ F = F /\ F[2] = 0 /\ F[1] = 0
ASSUME Test
Init == x = 0
Next == x' = x
====
