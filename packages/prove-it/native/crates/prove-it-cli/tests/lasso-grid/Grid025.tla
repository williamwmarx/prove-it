---- MODULE Grid025 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
A0 == x = 0 /\ x' = (x + 1) % 3 /\ y' = 1
A1 == x = 2 /\ x' = 0 /\ y' = 0
Next == A0 \/ A1
Spec == Init /\ [][Next]_vars /\ TRUE
P0 == <>[](x = 1)
P1 == []((x = 0) => <>[](y = 1))
====
