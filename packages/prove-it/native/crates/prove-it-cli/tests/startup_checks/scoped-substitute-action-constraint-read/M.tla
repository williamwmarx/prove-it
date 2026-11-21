---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
P == x' < 2
Q == x = 5
Init == x = 0
Next == x' = (x + 1) % 3 /\ (P \/ TRUE)

====
