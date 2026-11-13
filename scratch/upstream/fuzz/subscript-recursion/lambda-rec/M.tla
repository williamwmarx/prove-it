---- MODULE M ----
EXTENDS Naturals
VARIABLE x
RECURSIVE F(_)
Ap(Op(_), a) == Op(a)
F(n) == Ap(F, n)
Spec == x = 0 /\ [][x' = x]_<<x, F(0)>>
====
