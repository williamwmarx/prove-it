---- MODULE Grid072 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y \in {0, 1}
A0 == x # 0 /\ x' = 1 /\ y' \in {0, 1}
A1 == y = 1 /\ x' = 1 /\ y' = y
Next == A0 \/ A1
Spec == Init /\ [][Next]_vars /\ SF_vars(Next)
P0 == []<>(x = 0)
P1 == <>[](x = 1)
====
