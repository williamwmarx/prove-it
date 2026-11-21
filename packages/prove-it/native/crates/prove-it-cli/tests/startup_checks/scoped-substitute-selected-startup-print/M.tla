---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
P == x < 2
Q == FALSE
R == PrintT(P)
Inv == P \/ x = 2
Prop == []P
Init == x = 0
Next == x' = (x + 1) % 3 
====
