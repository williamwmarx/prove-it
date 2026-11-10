---- MODULE Grid052 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x \in {0, 1} /\ y = 0
A0 == x # 1 /\ y = 0 /\ x' \in {1, 2} /\ y' = 0
A1 == x = 0 /\ y = 0 /\ x' = (x + 1) % 3 /\ y' = y
Next == A0 \/ A1
Spec == Init /\ [][Next]_vars /\ SF_vars(Next)
P0 == []<>(x = 1 /\ y = 1)
P1 == []<>(x = 0)
====
