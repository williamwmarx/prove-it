---- MODULE Spec ----
EXTENDS Naturals
CONSTANT c, S, F(_), G
VARIABLE x, r, f
Init == x = 0
Next == x' = x
D0 == IF \E q \in G : F(x') THEN [F(1)]_@ ELSE (F(1) \/ "s")
D1 == ENABLED (1)
D2 == F(x')
====
