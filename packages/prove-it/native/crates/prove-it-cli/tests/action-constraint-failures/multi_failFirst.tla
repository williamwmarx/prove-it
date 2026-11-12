---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
IncX == x < 3 /\ x' = x + 1 /\ UNCHANGED y
IncY == y < 2 /\ y' = y + 1 /\ UNCHANGED x
Reset == x = 3 /\ x' = 0 /\ y' = 0
Next == IncX \/ IncY \/ Reset
Spec == Init /\ [][Next]_vars
FairSpec == Spec /\ WF_vars(Next)
A1 == x' < 2
A2 == x' = "s"
====
