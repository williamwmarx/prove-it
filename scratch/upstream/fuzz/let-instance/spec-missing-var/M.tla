---- MODULE M ----
EXTENDS Naturals
VARIABLES x, y
Spec == LET I == INSTANCE Inner WITH a <- x IN y = 0 /\ I!IInit /\ [][I!INext /\ UNCHANGED y]_I!vars
====
