---- MODULE Level029 ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x \in {0, 2}
Next == (x = 0 /\ x' \in {1, 4}) \/ (x = 1 /\ x' \in {0}) \/ (x = 2 /\ x' \in {3}) \/ (x = 3 /\ x' \in {4}) \/ (x = 4 /\ x' \in {2})
Spec == Init /\ [][Next]_x 
P == <>[](TLCGet("level") <= 4)
====
