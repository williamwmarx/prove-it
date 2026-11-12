---- MODULE Spec ----
EXTENDS Naturals
CONSTANT c, S, F(_), G
VARIABLE x, r, f
Init == x = 0
Next == x' = x
D0 == f[1]
D1 == q
D2 == [](\EE q : <<Init>>_x \/ ENABLED (x'))
ASSUME [q \in CHOOSE q \in S : Undef |-> [S]_F(1)]
====
