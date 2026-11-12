---- MODULE M ----
EXTENDS Naturals, Sequences, TLC
VARIABLE x
C == x < 10
Inv == C
E == Assert(FALSE, "m")
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_x
====
