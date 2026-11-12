---- MODULE Spec ----
EXTENDS Naturals
CONSTANT c, S, F(_), G
VARIABLE x, r, f
Init == x = 0
Next == x' = x
D0 == (c ~> x)
D1 == LET L(p) == CHOOSE q \in f[1] : F(x') IN L({})
ASSUME \E q \in SF_@(1) : q
====
