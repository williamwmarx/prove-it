---- MODULE Grid073 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
A0 == x # 1 /\ x' = x /\ y' = 0
A1 == y = 0 /\ x' \in {0, 2} /\ y' = (y + 1) % 2
A2 == x = 1 /\ x' = (x + 1) % 3 /\ y' \in {0, 1}
B(i) == x = i /\ x' = (i + 1) % 3 /\ y' = 1 - y
Next == A0 \/ A1 \/ A2 \/ \E i \in {0, 1} : B(i)
Spec == Init /\ [][Next]_vars /\ SF_vars(Next)
P0 == []<>(x # 0)
P1 == []((x = 0) => <>[](y = 1))
====
