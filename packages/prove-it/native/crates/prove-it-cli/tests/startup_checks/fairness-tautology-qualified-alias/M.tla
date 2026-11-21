---- MODULE M ----
EXTENDS Naturals
VARIABLE x
X == INSTANCE Aid WITH y <- x
Alias == X!L
Spec == x=0 /\ [][X!A]_x /\ Alias
====
