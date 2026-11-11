---- MODULE M ----
EXTENDS Naturals, TLC, TLCExt, Sequences, FiniteSets
VARIABLE x
C == TRUE
D == PrintT("d")
F(a, b) == LET z == b IN a
Init == x = 0 /\ (F(TRUE, C))
Next == x' = x

Spec == Init /\ [][Next]_x

====
