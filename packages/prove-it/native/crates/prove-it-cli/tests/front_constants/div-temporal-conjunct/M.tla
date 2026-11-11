---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = 1 - x
Spec == Init /\ [][Next]_x
P == <>[](x = 1 /\ (1 \div 0) > 0)
====
