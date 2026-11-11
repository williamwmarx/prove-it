---- MODULE Level004 ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x \in {1}
Next == (x = 0 /\ x' \in {1}) \/ (x = 1 /\ x' \in {0}) \/ (x = 2 /\ x' \in {0, 1})
Spec == Init /\ [][Next]_x 
P == [](x = 1 => <>(TLCGet("level") = 2))
====
