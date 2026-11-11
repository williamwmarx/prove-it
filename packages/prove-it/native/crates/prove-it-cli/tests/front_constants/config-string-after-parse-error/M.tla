---- MODULE M ----
EXTENDS Naturals, TLC, Sequences, FiniteSets
CONSTANT K
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_x
Inv == PrintT(K) /\ TRUE

====
