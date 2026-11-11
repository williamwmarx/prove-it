---- MODULE M ----
EXTENDS Naturals, TLC, Sequences, FiniteSets, TLCExt
VARIABLE x
C == 1
D == PrintT("d")
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_x

====
