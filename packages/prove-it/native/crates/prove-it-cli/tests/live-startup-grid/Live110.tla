---- MODULE Live110 ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_x
I == INSTANCE Live110B WITH C <- 2
P == I!Id(\A j \in I!D : [](x # j))
====
