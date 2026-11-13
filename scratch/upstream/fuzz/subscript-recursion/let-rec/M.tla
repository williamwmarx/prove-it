---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Spec == LET RECURSIVE G(_)
            G(n) == G(n)
        IN x = 0 /\ [][x' = x]_<<x, G(0)>>
====
