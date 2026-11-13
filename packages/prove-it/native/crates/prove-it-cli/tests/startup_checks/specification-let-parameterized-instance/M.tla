---- MODULE M ----
EXTENDS Naturals
VARIABLES x, y
Spec == LET P(v) == INSTANCE Inner WITH a <- v IN P(x)!IInit /\ y = 0 /\ [][P(x)!INext /\ UNCHANGED y]_<<x, y>>
====
