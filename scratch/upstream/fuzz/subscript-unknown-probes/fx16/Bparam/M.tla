---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Spec == x = 0 /\ [][x' = x]_(LET P(z) == INSTANCE Inner WITH v <- z IN P(x)!vars)
====
