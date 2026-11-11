---- MODULE Grid037 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x \in {0, 1} /\ y = 0
A0 == x # 1 /\ x' = x /\ y' \in {0, 1}
A1 == y = 1 /\ x' \in {0, 2} /\ y' = 0
A2 == x' = (x + 1) % 3 /\ y' = 1
A3 == y = 0 /\ x' = 0 /\ y' = 1
Next == A0 \/ A1 \/ A2 \/ A3
Spec == Init /\ [][Next]_vars /\ WF_vars(A1) /\ WF_vars(A0)
P0 == []((x = 0) => <>[](y = 1))
====
