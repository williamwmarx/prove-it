---- MODULE Spec ----
EXTENDS Naturals
CONSTANT c, S, F(_), G
VARIABLE x, r, f
Init == x = 0
Next == x' = x
D0 == f[1]
D1 == \EE q : SF_[q \in F(x') |-> Next](LET L(p) == @ IN L(Undef))
====
