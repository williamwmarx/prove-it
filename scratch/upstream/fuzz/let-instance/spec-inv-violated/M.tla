---- MODULE M ----
EXTENDS Naturals
VARIABLES x, y
Spec == LET I == INSTANCE Inner WITH a <- x IN I!IInit /\ y = 0 /\ [][I!INext /\ UNCHANGED y]_<<x, y>>
Inv == LET I == INSTANCE Inner WITH a <- x IN I!Inv
====
