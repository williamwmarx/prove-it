---- MODULE Level024 ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x \in {1}
Next == (x = 0 /\ x' \in {1, 2}) \/ (x = 1 /\ x' \in {2}) \/ (x = 2 /\ x' \in {1})
Spec == Init /\ [][Next]_x 
P == <>[](x # 2 \/ TLCGet("level") > 5)
====
