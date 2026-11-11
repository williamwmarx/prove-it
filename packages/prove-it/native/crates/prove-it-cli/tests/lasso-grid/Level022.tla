---- MODULE Level022 ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x \in {1, 3}
Next == (x = 0 /\ x' \in {3}) \/ (x = 1 /\ x' \in {0}) \/ (x = 2 /\ x' \in {1, 3}) \/ (x = 3 /\ x' \in {0, 1})
Spec == Init /\ [][Next]_x /\ SF_x(Next)
P == []<><<TLCGet("level")' > TLCGet("level") + 0>>_x
====
