---- MODULE Spec ----
EXTENDS Naturals
CONSTANT c, S, F(_), G
VARIABLE x, r, f
Init == x = 0
Next == x' = x
D0 == Nat
D1 == LET L(p) == (x')' IN L(CHOOSE q \in (S)' : SF_@(1))
D2 == (@)'
ASSUME WF_x((<<>> \/ "s"))
====
