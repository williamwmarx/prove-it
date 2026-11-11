---- MODULE Level008 ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x \in {0, 4}
Next == (x = 0 /\ x' \in {2, 3}) \/ (x = 1 /\ x' \in {2, 3}) \/ (x = 2 /\ x' \in {3, 4}) \/ (x = 3 /\ x' \in {0}) \/ (x = 4 /\ x' \in {1})
Spec == Init /\ [][Next]_x /\ SF_x(Next)
P == [](x = 0 => <>(TLCGet("level") = 2))
====
