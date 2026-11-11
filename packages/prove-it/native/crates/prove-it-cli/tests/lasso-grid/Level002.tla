---- MODULE Level002 ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x \in {2}
Next == (x = 0 /\ x' \in {1, 2}) \/ (x = 1 /\ x' \in {0, 2}) \/ (x = 2 /\ x' \in {0, 3}) \/ (x = 3 /\ x' \in {1})
Spec == Init /\ [][Next]_x /\ SF_x(Next)
P == []<>(TLCGet("level") > 1)
====
