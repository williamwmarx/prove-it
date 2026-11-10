---- MODULE Grid150 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
A0 == x = 1 /\ y = 1 /\ x' = x /\ y' \in {0, 1}
A1 == x # 0 /\ y = 0 /\ x' = x /\ y' = 1
Next == A0 \/ A1
Spec == Init /\ [][Next]_vars /\ TRUE
P0 == <>[](x = 1)
====
