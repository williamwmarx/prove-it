---- MODULE M ----
EXTENDS Naturals, TLC, Sequences, FiniteSets
CONSTANT C
VARIABLE x
D == 1 \div 0 = 1
Init == x = 0
Next == x' = x
Spec == C /\ Init /\ [][Next]_x
====
