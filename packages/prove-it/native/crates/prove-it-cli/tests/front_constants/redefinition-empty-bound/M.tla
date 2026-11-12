---- MODULE M ----
EXTENDS Naturals, TLC, TLCExt, Sequences, FiniteSets
VARIABLE x
C == TRUE
D == PrintT("d")

Init == x = 0 /\ (~\E i \in {} : C)
Next == x' = x

Spec == Init /\ [][Next]_x

====
