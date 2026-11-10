---- MODULE Grid079 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
A0 == x = 2 /\ x' = 2 /\ y' = 0
A1 == x # 1 /\ y = 0 /\ x' = x /\ y' = 1
Next == A0 \/ A1
Spec == Init /\ [][Next]_vars /\ WF_vars(A0) /\ WF_vars(A1)
P0 == <>[](y = 0) \/ []<>(x = 2)
P1 == []((x = 0) => <>[](y = 1))
====
