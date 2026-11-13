---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Spec == x = 0 /\ [][x' = x]_(LET f[i \in {0}] == i IN x)
====
