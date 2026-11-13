---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
S == LET I == INSTANCE Inner WITH a <- x IN I!ISpec
Spec == S
====
