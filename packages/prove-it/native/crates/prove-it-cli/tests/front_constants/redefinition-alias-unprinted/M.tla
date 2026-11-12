---- MODULE M ----
EXTENDS Naturals, TLC, Sequences, FiniteSets
VARIABLE x
C == 5
D == PrintT("d")
Al == [x |-> x, c |-> C]
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_x

====
