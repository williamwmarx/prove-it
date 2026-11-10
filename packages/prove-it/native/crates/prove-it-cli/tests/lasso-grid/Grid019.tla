---- MODULE Grid019 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y \in {0, 1}
A0 == x' = (x + 1) % 3 /\ y' = y
A1 == x' = 0 /\ y' = 1
Next == A0 \/ A1
Spec == Init /\ [][Next]_vars /\ SF_vars(Next)
P0 == []<>(x = 0)
P1 == (x = 2) ~> (y = 0)
====
