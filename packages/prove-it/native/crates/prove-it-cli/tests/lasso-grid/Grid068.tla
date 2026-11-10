---- MODULE Grid068 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
A0 == x = 1 /\ y = 1 /\ x' = x /\ y' = y
A1 == x = 1 /\ x' = x /\ y' \in {0, 1}
B(i) == x = i /\ x' = (i + 1) % 3 /\ y' = 1 - y
Next == A0 \/ A1 \/ \E i \in {0, 1} : B(i)
Spec == Init /\ [][Next]_vars /\ WF_vars(A0) /\ WF_vars(A1)
P0 == []<>(y = 1)
P1 == []((x = 0) => <>[](y = 1))
====
