---- MODULE Level006 ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x \in {0}
Next == (x = 0 /\ x' \in {1, 2}) \/ (x = 1 /\ x' \in {0, 2}) \/ (x = 2 /\ x' \in {0}) \/ (x = 3 /\ x' \in {2})
Spec == Init /\ [][Next]_x 
P == (TLCGet("level") = 1) ~> (TLCGet("level") >= 3)
====
