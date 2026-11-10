---- MODULE Grid082 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
A0 == x = 0 /\ x' \in {0, 1} /\ y' = 1
A1 == x # 1 /\ x' = x /\ y' = 0
Next == A0 \/ A1
Spec == Init /\ [][Next]_vars /\ SF_vars(Next)
P0 == <>[](y = 0) \/ []<>(x = 2)
====
