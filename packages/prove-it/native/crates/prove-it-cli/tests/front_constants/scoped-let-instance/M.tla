---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 0
Next == x' = x
ASSUME LET I == INSTANCE fx WITH N <- 3 IN PrintT(I!Get) /\ I!Get = 5
====
