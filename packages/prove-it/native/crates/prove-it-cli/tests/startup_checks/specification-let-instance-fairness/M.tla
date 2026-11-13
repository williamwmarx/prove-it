---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_x /\ (LET I == INSTANCE Inner WITH a <- x IN WF_x(I!Act))
P == <>(x = 2)
====
