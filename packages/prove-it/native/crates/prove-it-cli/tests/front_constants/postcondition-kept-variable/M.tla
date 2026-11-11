---- MODULE M ----
EXTENDS Naturals, TLC, Sequences, FiniteSets
VARIABLE x
C == x < 10
D == TLCEval(Print(x, TRUE))
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_x

====
