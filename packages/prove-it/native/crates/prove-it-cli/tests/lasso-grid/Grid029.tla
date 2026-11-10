---- MODULE Grid029 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y \in {0, 1}
A0 == y = 0 /\ x' = x /\ y' = (y + 1) % 2
A1 == x # 1 /\ x' \in {1, 2} /\ y' = 1
A2 == y = 1 /\ x' = x /\ y' = 0
Next == A0 \/ A1 \/ A2
Spec == Init /\ [][Next]_vars /\ SF_vars(Next)
P0 == []<>(y = 1)
P1 == []<>(x = 0)
====
