---- MODULE M ----
EXTENDS Naturals, TLC, Sequences, FiniteSets
VARIABLE x
C == 5
D == TLCEval(PrintT("d"))
Inv == TRUE
Init == x = 0
Next == x' = (x + 1) % 3 /\ C = C
Spec == Init /\ [][Next]_x

====
