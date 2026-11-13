---- MODULE M ----
EXTENDS Naturals
VARIABLES x, y
Spec == x = 0 /\ y = 0 /\ [][x' = (x + 1) % 3 /\ UNCHANGED y]_<<x, y>>
Inv == LET Q(v) == INSTANCE Inner WITH a <- v IN Q(x)!Inv
====
