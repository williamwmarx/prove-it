---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
P == x < 2
Q == FALSE
Init == x = 0
Next == x' = (x + 1) % 3 /\ PrintT(P)

====
