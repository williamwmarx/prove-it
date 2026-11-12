---- MODULE Live112 ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_x
I == INSTANCE Live112B WITH C <- 2
P == I!Q(I!Snd)
====
