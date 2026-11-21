---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
z == [b |-> 0]
Init == x = 0
Next == x' = x
ASSUME LET Op(f) == PrintT(f) /\ f[1] = f[1] IN Op([x1 \in 1..2 |-> [a |-> x1, b |-> x1]])
====
