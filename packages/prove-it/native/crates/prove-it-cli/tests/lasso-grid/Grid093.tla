---- MODULE Grid093 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x \in {0, 1} /\ y = 0
A0 == y = 0 /\ x' = (x + 1) % 3 /\ y' = 1
A1 == x = 0 /\ x' = 1 /\ y' = (y + 1) % 2
A2 == x' = 2 /\ y' = y
A3 == x = 0 /\ y = 1 /\ x' = x /\ y' = (y + 1) % 2
B(i) == x = i /\ x' = (i + 1) % 3 /\ y' = 1 - y
Next == A0 \/ A1 \/ A2 \/ A3 \/ \E i \in {0, 1} : B(i)
Spec == Init /\ [][Next]_vars /\ WF_vars(A3) /\ WF_vars(A3)
P0 == []((x = 0) => <>[](y = 1))
====
