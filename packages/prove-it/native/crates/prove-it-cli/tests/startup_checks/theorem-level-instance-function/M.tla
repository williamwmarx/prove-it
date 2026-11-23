---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
I(k) == INSTANCE N WITH k <- k
C == PrintT("c") /\ (I(1)!F[0] = 0)
Init == x = 0
Next == x' = x
Inv == C \/ TRUE
====
