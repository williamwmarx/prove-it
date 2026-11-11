---- MODULE Level003 ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x \in {0, 1}
Next == (x = 0 /\ x' \in {2}) \/ (x = 1 /\ x' \in {0, 2}) \/ (x = 2 /\ x' \in {0})
Spec == Init /\ [][Next]_x /\ SF_x(Next)
P == (TLCGet("level") = 1) ~> (TLCGet("level") >= 1)
====
