---- MODULE Level033 ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x \in {1, 2}
Next == (x = 0 /\ x' \in {2}) \/ (x = 1 /\ x' \in {2}) \/ (x = 2 /\ x' \in {1, 3}) \/ (x = 3 /\ x' \in {1, 2})
Spec == Init /\ [][Next]_x 
P == []<><<TLCGet("level")' = 5>>_x
====
