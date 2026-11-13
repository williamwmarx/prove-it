---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_x
Inv == LET I == INSTANCE Inner WITH a <- x IN I!Inv
====
