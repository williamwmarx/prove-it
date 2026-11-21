---- MODULE M ----
EXTENDS Naturals
VARIABLE x
I == INSTANCE Sm WITH N <- 0
Init == x = I!V(1)!L
Next == x' = x
====
