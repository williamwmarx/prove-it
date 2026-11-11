---- MODULE Level017 ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x \in {1, 4}
Next == (x = 0 /\ x' \in {2}) \/ (x = 1 /\ x' \in {0, 3}) \/ (x = 2 /\ x' \in {4}) \/ (x = 3 /\ x' \in {1}) \/ (x = 4 /\ x' \in {2})
Spec == Init /\ [][Next]_x /\ SF_x(Next)
P == [](x = 3 => <>(TLCGet("level") = 1))
====
