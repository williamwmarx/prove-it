---- MODULE M ----
EXTENDS Naturals
VARIABLES x, y
CONSTANT C, G
D1 == y
D2 == 1
D3 == <<y>>
D4 == C
D5 == <<x, y>>
S(v) == x = 0 /\ y = 0 /\ [][x' = x /\ y' = y]_<<x, v>>
S2(w) == LET K == w IN S(K)
Spec == LET L == 1 IN S2(L)
====
