---- MODULE Grid061 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
A0 == x' = x /\ y' \in {0, 1}
A1 == x # 0 /\ x' = x /\ y' = 0
A2 == y = 0 /\ x' = (x + 1) % 3 /\ y' = y
Next == A0 \/ A1 \/ A2
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
P0 == []((x = 0) => <>[](y = 1))
P1 == []<>(y = 1)
====
