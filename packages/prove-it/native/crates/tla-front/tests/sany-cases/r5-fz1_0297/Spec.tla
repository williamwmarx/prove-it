---- MODULE Spec ----
EXTENDS Naturals
CONSTANT c, S, F(_), G
VARIABLE x, r, f
Init == x = 0
Next == x' = x
D0 == (Init)'
D1 == UNCHANGED [(<<>> ~> Undef)]_[q \in 1 |-> x']
====
