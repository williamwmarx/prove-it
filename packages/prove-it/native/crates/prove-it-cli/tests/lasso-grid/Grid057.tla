---- MODULE Grid057 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
A0 == y = 0 /\ x' = x /\ y' \in {0, 1}
A1 == x = 0 /\ y = 1 /\ x' = (x + 1) % 3 /\ y' = (y + 1) % 2
A2 == x = 1 /\ y = 0 /\ x' = (x + 1) % 3 /\ y' = 0
Next == A0 \/ A1 \/ A2
Spec == Init /\ [][Next]_vars /\ SF_vars(Next)
P0 == []((x = 0) => <>[](y = 1))
P1 == []<>(x = 1 /\ y = 1)
====
