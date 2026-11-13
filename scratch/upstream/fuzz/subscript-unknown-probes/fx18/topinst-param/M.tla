---- MODULE M ----
EXTENDS Naturals, Sequences
VARIABLES x, y
T(z) == INSTANCE Inner WITH v <- z
Spec == x = 0 /\ y = 0 /\ [][x' = x /\ y' = y]_(T(<<x, y>>)!vars)
====
