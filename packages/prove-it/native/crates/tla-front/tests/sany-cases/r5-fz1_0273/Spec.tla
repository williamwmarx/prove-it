---- MODULE Spec ----
EXTENDS Naturals
CONSTANT c, S, F(_), G
VARIABLE x, r, f
Init == x = 0
Next == x' = x
D0 == F(1)
D1 == SF_@((F(1))')
D2 == <<>>
====
