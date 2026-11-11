---- MODULE Level009 ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x \in {2}
Next == (x = 0 /\ x' \in {1, 2}) \/ (x = 1 /\ x' \in {0}) \/ (x = 2 /\ x' \in {1}) \/ (x = 3 /\ x' \in {0, 2})
Spec == Init /\ [][Next]_x /\ WF_x(Next)
P == []<><<TLCGet("level")' > TLCGet("level") + 0>>_x
====
