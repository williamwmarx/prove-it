---- MODULE Level012 ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x \in {4}
Next == (x = 0 /\ x' \in {1}) \/ (x = 1 /\ x' \in {0}) \/ (x = 2 /\ x' \in {3}) \/ (x = 3 /\ x' \in {1, 2}) \/ (x = 4 /\ x' \in {1, 3})
Spec == Init /\ [][Next]_x 
P == <>(TLCGet("level") = 3)
====
