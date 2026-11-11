---- MODULE M ----
EXTENDS Naturals, TLC, Sequences, FiniteSets
CONSTANT C
VARIABLE x
D == <<TRUE>>
Init == x = 0
Next == x' = x
Spec == C /\ Init /\ [][Next]_x
====
