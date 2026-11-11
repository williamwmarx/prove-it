---- MODULE Spec ----
EXTENDS Naturals
CONSTANT c, S, F(_), G
VARIABLE x, r, f
Init == x = 0
Next == x' = x
D0 == (SF_[q \in (1 \/ F(x')) |-> SF_x(c)]((LET L(p) == f[1] IN L(1) \cdot IF S THEN f[1] ELSE F(x'))) \cdot lab:: [q \in (S \cdot 1) |-> (r.a ~> <<>>)])
D1 == Next
====
