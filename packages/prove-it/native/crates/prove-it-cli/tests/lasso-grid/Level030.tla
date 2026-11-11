---- MODULE Level030 ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x \in {0, 4}
Next == (x = 0 /\ x' \in {1, 4}) \/ (x = 1 /\ x' \in {2, 3}) \/ (x = 2 /\ x' \in {0}) \/ (x = 3 /\ x' \in {1, 2}) \/ (x = 4 /\ x' \in {0})
Spec == Init /\ [][Next]_x /\ WF_x(Next)
P == []<><<TLCGet("level")' = 3>>_x
====
