---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x = 0 /\ x' = 1
G(Op(_)) == x = 1
K(a) == x' = a
H == G(K)
====
