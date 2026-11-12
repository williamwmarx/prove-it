---- MODULE Spec ----
EXTENDS Naturals
CONSTANT c, S, F(_), G
VARIABLE x, r, f
Init == x = 0
Next == x' = x
D0 == [((Nat /\ S) \cdot F(1))]_[q \in \E q \in F(1) : TRUE |-> UNCHANGED x]
D1 == r.a
D2 == WF_x(Next)
====
