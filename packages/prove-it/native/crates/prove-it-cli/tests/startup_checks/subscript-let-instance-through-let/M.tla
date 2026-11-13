---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Spec == x = 0 /\ [][x' = x]_(LET I == INSTANCE Inner WITH v <- x IN LET K == I!vars IN K)
====
