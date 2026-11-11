---- MODULE Level025 ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x \in {0}
Next == (x = 0 /\ x' \in {2}) \/ (x = 1 /\ x' \in {2}) \/ (x = 2 /\ x' \in {3}) \/ (x = 3 /\ x' \in {2}) \/ (x = 4 /\ x' \in {0, 1})
Spec == Init /\ [][Next]_x /\ WF_x(Next)
P == [](x = 0 => <>(TLCGet("level") = 2))
====
