---- MODULE Level011 ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x \in {3}
Next == (x = 0 /\ x' \in {1, 3}) \/ (x = 1 /\ x' \in {2}) \/ (x = 2 /\ x' \in {0, 1}) \/ (x = 3 /\ x' \in {1})
Spec == Init /\ [][Next]_x 
P == <>(TLCGet("level") = 5)
====
