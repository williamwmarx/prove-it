---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
z == [b |-> 0]
Init == x = 0
Next == x' = x
ASSUME LET Op(f) == f[1] = f[1] IN Op([y \in 1..2 |-> [a |-> y, b |-> y]]) /\ PrintT([y \in 1..2 |-> [a |-> y, b |-> y]])
====
