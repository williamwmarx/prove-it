---- MODULE Level023 ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x \in {0}
Next == (x = 0 /\ x' \in {1, 2}) \/ (x = 1 /\ x' \in {0}) \/ (x = 2 /\ x' \in {0})
Spec == Init /\ [][Next]_x /\ WF_x(Next)
P == []<><<TLCGet("level")' = 3>>_x
====
