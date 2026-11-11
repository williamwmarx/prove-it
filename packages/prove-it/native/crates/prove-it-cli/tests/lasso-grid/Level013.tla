---- MODULE Level013 ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x \in {1}
Next == (x = 0 /\ x' \in {1}) \/ (x = 1 /\ x' \in {2}) \/ (x = 2 /\ x' \in {0, 1}) \/ (x = 3 /\ x' \in {0, 1})
Spec == Init /\ [][Next]_x /\ SF_x(Next)
P == []<><<TLCGet("level")' > TLCGet("level") + 1>>_x
====
