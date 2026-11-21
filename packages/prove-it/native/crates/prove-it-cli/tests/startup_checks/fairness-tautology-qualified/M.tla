---- MODULE M ----
EXTENDS Naturals
VARIABLE x
X == INSTANCE Aux WITH y <- x
Alias == X!L
Spec == x=0 /\ [][X!A]_x /\ X!L
====
