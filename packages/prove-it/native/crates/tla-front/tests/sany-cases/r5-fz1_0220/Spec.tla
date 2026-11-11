---- MODULE Spec ----
EXTENDS Naturals
CONSTANT c, S, F(_), G
VARIABLE x, r, f
Init == x = 0
Next == x' = x
D0 == \EE q : Init
D1 == ENABLED (TRUE)
D2 == \E q \in [](Undef \cdot G) : SF_{@, (Init \cdot @)}(lab:: (x \cdot x'))
THEOREM f[1]
====
