---- MODULE M ----
EXTENDS Naturals
VARIABLE x
A == x < 2 /\ x' = x + 1
L == WF_x(A)
Alias == L
Id(a) == a
Pair(a,b) == a /\ b
Spec == x = 0 /\ [][A]_x /\ (L /\ WF_x(A))
====
