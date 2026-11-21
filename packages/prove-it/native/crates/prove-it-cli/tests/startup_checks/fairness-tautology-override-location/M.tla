---- MODULE M ----
EXTENDS Naturals
VARIABLE x
A == x < 2 /\ x' = x + 1
L == WF_x(A)
Alias == L
Other == SF_x(A)
Spec == x=0 /\ [][A]_x /\ L
====
