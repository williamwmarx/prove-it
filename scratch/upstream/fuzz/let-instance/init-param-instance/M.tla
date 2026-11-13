---- MODULE M ----
EXTENDS Naturals
VARIABLES x, y
Init == LET Q(v) == INSTANCE Inner WITH a <- v IN Q(x)!IInit /\ y = 0
Next == x' = (x + 1) % 3 /\ UNCHANGED y
====
