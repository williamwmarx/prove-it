---- MODULE Spec ----
EXTENDS Naturals
CONSTANT c, S, F(_), G
VARIABLE x, r, f
Init == x = 0
Next == x' = x
D0 == ((Next + 1) => []1)
D1 == F(1)
D2 == \EE q : UNCHANGED lab:: (F(1) ~> <<>>)
====
