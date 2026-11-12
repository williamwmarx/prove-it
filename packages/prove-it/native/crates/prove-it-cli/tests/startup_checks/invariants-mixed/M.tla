---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
A == 1 + 1 = 2
B == Print("b", TRUE)
C == x >= 0
D == {1} = {1}
P == x >= 0
====
