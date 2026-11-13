---- MODULE M ----
EXTENDS Naturals
VARIABLES x, y
Spec == LET I == INSTANCE Inner WITH a <- x IN I!ISpec /\ y = 0 /\ [][y' = y]_y
P == <>(x = 2)
====
