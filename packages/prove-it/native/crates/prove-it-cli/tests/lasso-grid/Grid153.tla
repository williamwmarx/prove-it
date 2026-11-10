---- MODULE Grid153 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
A0 == x = 1 /\ y = 0 /\ x' = 0 /\ y' = 0
A1 == y = 0 /\ x' = (x + 1) % 3 /\ y' = (y + 1) % 2
Next == A0 \/ A1
Spec == Init /\ [][Next]_vars /\ TRUE
P0 == <>[](x = 1)
P1 == []<>(x # 0)
====
