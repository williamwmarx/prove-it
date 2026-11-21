---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
z == [b |-> 0]
Init == x = 0
Next == x' = x
ASSUME LET g == [y \in 1..2 |-> [a |-> y, b |-> y]] h == g IN h[1] = h[1] /\ PrintT(h)
====
