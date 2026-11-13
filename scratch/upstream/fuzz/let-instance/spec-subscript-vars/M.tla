---- MODULE M ----
EXTENDS Naturals
VARIABLES x, y
Spec == LET I == INSTANCE Inner WITH a <- x IN I!ISpec2 /\ y = 0
====
