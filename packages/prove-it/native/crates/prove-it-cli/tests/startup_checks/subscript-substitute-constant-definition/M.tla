---- MODULE M ----
EXTENDS Naturals
VARIABLES x, y
CONSTANT C, G
D1 == y
D2 == 1
D3 == <<y>>
D4 == C
D5 == <<x, y>>
Spec == x = 0 /\ y = 0 /\ [][x' = x /\ y' = y]_G
====
