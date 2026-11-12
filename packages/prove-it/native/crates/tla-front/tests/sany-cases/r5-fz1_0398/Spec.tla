---- MODULE Spec ----
EXTENDS Naturals
CONSTANT c, S, F(_), G
VARIABLE x, r, f
Init == x = 0
Next == x' = x
D0 == ([q \in c |-> {}] \/ @)
D1 == ENABLED ([q \in r.a |-> G])
D2 == [r.a]_@
====
