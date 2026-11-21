---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Init == x = FALSE
Spec == LET A == x' = x IN Init /\ [][A \/ x]_x
====
