---- MODULE Grid053 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x \in {0, 1} /\ y = 0
A0 == x = 2 /\ y = 0 /\ x' = (x + 1) % 3 /\ y' = y
A1 == x # 2 /\ y = 0 /\ x' = x /\ y' \in {0, 1}
Next == A0 \/ A1
Spec == Init /\ [][Next]_vars /\ WF_vars(A1) /\ WF_vars(A1)
P0 == []<>(x = 0)
P1 == <>[](x = 1)
====
