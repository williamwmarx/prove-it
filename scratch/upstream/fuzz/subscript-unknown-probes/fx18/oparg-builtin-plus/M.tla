---- MODULE M ----
EXTENDS Naturals, Sequences
VARIABLES x, y
Ap2(F(_, _)) == <<x, y, F(1, 2)>>
Spec == x = 0 /\ y = 0 /\ [][x' = x /\ y' = y]_(Ap2(+))
====
