---- MODULE Probe ----
EXTENDS TLC, Integers
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 2
B == PrintT(7)
K == x = 0
I == INSTANCE Base
Inv == PrintT(I!J)
====
