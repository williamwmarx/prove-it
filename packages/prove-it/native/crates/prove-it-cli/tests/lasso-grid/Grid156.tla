---- MODULE Grid156 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y \in {0, 1}
A0 == x = 2 /\ x' \in {0, 2} /\ y' = (y + 1) % 2
A1 == x' = x /\ y' = (y + 1) % 2
A2 == x' = 2 /\ y' = y
B(i) == x = i /\ x' = (i + 1) % 3 /\ y' = 1 - y
Next == A0 \/ A1 \/ A2 \/ \E i \in {0, 1} : B(i)
Spec == Init /\ [][Next]_vars /\ WF_vars(A2) /\ WF_vars(A1)
P0 == []((x = 0) => <>[](y = 1))
P1 == []<>(x = 1 /\ y = 1)
====
