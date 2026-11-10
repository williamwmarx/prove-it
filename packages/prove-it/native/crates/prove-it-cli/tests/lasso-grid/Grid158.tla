---- MODULE Grid158 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
A0 == x # 2 /\ x' = (x + 1) % 3 /\ y' = 1
A1 == x = 1 /\ x' = 2 /\ y' = y
Next == A0 \/ A1
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
P0 == []<>(x = 0)
====
