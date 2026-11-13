---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Spec == x = 0 /\ [][x' = x]_(LET RECURSIVE g(_)
                g(n) == n IN x)
====
