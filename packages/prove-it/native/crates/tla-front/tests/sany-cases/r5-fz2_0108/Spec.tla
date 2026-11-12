---- MODULE Spec ----
EXTENDS Naturals
CONSTANT c, S, F(_), G
VARIABLE x, r, f
Init == x = 0
Next == x' = x
D0 == [q]_F(x')
D1 == (1 ~> G)
ASSUME ((x \/ c) ~> \EE q : 1)
====
