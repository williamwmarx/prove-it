---- MODULE M ----
EXTENDS Naturals, TLC, Sequences, FiniteSets
VARIABLE x
C == 5
D == TLCEval(PrintT("d"))
Inv == \A i \in {1, 2} : C = C
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_x

====
