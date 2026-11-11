---- MODULE Level035 ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x \in {0}
Next == (x = 0 /\ x' \in {1, 3}) \/ (x = 1 /\ x' \in {0}) \/ (x = 2 /\ x' \in {0, 1}) \/ (x = 3 /\ x' \in {0}) \/ (x = 4 /\ x' \in {0, 3})
Spec == Init /\ [][Next]_x /\ SF_x(Next)
P == <>[](TLCGet("level") <= 1)
====
