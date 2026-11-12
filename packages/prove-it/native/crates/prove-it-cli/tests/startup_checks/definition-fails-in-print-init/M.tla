---- MODULE M ----
EXTENDS Naturals, Sequences, TLC
VARIABLE x
D == PrintT(CHOOSE y \in {} : TRUE)

Init == x = 0 /\ D
Next == x' = 1 - x

====
