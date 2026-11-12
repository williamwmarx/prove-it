---- MODULE Live114 ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_x
I == INSTANCE Live114B WITH C <- 2
P == I!Q({}) /\ <>(x = 5)
====
