---- MODULE Level034 ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x \in {1, 2}
Next == (x = 0 /\ x' \in {1}) \/ (x = 1 /\ x' \in {0}) \/ (x = 2 /\ x' \in {0, 1})
Spec == Init /\ [][Next]_x /\ WF_x(Next)
P == (TLCGet("level") = 1) ~> (TLCGet("level") >= 1)
====
