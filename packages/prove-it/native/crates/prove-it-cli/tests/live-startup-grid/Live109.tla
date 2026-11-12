---- MODULE Live109 ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_x
I == INSTANCE Live109B WITH C <- 2
G(a) == I!D
P == I!Q(G)
====
