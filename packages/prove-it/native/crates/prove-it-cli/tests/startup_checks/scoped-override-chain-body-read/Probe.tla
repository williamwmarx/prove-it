---- MODULE Probe ----
EXTENDS Integers, TLC
K == TRUE
B == FALSE
VARIABLE x
Init == x = 0
Next == x' = x
I == INSTANCE Base
ASSUME PrintT(I!J)

====
