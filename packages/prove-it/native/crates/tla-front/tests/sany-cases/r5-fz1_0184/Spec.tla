---- MODULE Spec ----
EXTENDS Naturals
CONSTANT c, S, F(_), G
VARIABLE x, r, f
Init == x = 0
Next == x' = x
D0 == [q \in c |-> IF <>([c]_@) THEN ((Next => @) /\ [c]_S) ELSE [(F(x') => G)]_<<>>]
D1 == r.a
D2 == WF_x(Undef)
ASSUME c
====
