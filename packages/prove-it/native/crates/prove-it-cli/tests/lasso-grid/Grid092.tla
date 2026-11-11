---- MODULE Grid092 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
A0 == x # 2 /\ x' = (x + 1) % 3 /\ y' = (y + 1) % 2
A1 == x # 0 /\ x' = 2 /\ y' = 1
A2 == y = 1 /\ x' = 0 /\ y' = (y + 1) % 2
B(i) == x = i /\ x' = (i + 1) % 3 /\ y' = 1 - y
Next == A0 \/ A1 \/ A2 \/ \E i \in {0, 1} : B(i)
Spec == Init /\ [][Next]_vars /\ SF_vars(Next)
P0 == (x = 2) ~> (y = 0)
====
