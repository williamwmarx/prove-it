---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
Spec == LET K == 1 IN LET I == INSTANCE Inner WITH a <- x IN I!ISpec
====
