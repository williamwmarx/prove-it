---- MODULE Probe ----
EXTENDS Integers, TLC
VARIABLE x
Init == x = 0
Next == x' = x
F == FALSE
K == 3
B2 == TRUE
I == INSTANCE Base
ASSUME PrintT(I!K)
====
