---- MODULE M ----
EXTENDS Naturals
VARIABLES x, y
Spec == LET I == INSTANCE Inner WITH a <- x
            J == INSTANCE Inner WITH a <- y
        IN I!IInit /\ J!IInit /\ [][I!INext /\ J!INext]_<<x, y>>
====
