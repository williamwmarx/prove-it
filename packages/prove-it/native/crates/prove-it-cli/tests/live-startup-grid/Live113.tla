---- MODULE Live113 ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_x
I == INSTANCE Live113B WITH C <- 2
J == INSTANCE Live113B WITH C <- 1
P == I!In!R(J!D)
====
