---- MODULE M ----
EXTENDS Naturals, TLC, A
VARIABLE x
C == 5
D == 7
PM == PrintT("pm")
In == INSTANCE I
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_x

====
