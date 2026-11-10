---- MODULE Grid047 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
A0 == x = 0 /\ x' \in {1, 2} /\ y' = y
A1 == y = 1 /\ x' = 0 /\ y' = y
A2 == y = 1 /\ x' = 1 /\ y' = 0
A3 == x' = 0 /\ y' \in {0, 1}
Next == A0 \/ A1 \/ A2 \/ A3
Spec == Init /\ [][Next]_vars /\ WF_vars(A0) /\ WF_vars(A1)
P0 == <>[](y = 0) \/ []<>(x = 2)
P1 == []((x = 0) => <>[](y = 1))
====
