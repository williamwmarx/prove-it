---- MODULE Grid149 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y \in {0, 1}
A0 == x' = 2 /\ y' \in {0, 1}
A1 == y = 1 /\ x' \in {0, 2} /\ y' = (y + 1) % 2
A2 == x # 2 /\ x' = 2 /\ y' = 1
Next == A0 \/ A1 \/ A2
Spec == Init /\ [][Next]_vars /\ SF_vars(Next)
P0 == []<>(x # 0)
P1 == (x = 2) ~> (y = 0)
====
