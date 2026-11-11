---- MODULE M ----
EXTENDS Naturals, TLC, Sequences, FiniteSets
VARIABLE x
D == TLCEval(PrintT("d"))
C == 5
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_x

====
