---- MODULE M ----
EXTENDS Naturals, TLC, Sequences, FiniteSets
VARIABLE x
C == 5
Z == PrintT("z")
D == TLCEval(PrintT("d"))
Inv == C = C
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_x

====
