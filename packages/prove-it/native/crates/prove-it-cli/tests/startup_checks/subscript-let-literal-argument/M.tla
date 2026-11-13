---- MODULE M ----
EXTENDS Naturals
VARIABLE x
S(v) == x = 0 /\ [][x' = x]_<<x, v>>
Spec == LET L == 1 IN S(L)
====
