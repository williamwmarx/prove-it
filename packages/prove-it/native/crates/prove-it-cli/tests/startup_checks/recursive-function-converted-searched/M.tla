---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
F[n \in 1..2] == IF PrintT(n) /\ n = 1 THEN 1 ELSE F[n - 1]
Converted == F[2] = 1 /\ F = F
Init == x \in 1..2
Next == x' = F[x]
Inv == F[x] = 1
====
