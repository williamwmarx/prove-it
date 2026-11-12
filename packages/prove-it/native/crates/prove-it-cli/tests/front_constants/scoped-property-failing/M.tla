---- MODULE M ----
EXTENDS Naturals, TLC, A
VARIABLE x
MK == 1
MV == 2
In == INSTANCE I
Pr == 1 \div 0 = 1
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_x

====
