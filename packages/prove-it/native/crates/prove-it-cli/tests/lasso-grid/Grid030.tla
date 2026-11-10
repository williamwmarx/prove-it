---- MODULE Grid030 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x \in {0, 1} /\ y = 0
A0 == x' = x /\ y' = y
A1 == x' = 2 /\ y' = 1
A2 == x' = (x + 1) % 3 /\ y' = (y + 1) % 2
Next == A0 \/ A1 \/ A2
Spec == Init /\ [][Next]_vars /\ TRUE
P0 == <>[](x = 1)
====
