---- MODULE PInEnumFcnEmpty ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {}
Init == x = 0
A == x' \in [{1} -> ({})]
B == x' = 0
E == x' = 1
Next == /\ (A \/ B \/ E)
Copy == x' \in [{1} -> ({})]
Weak == Init /\ [][Next]_x /\ WF_x(A)
AliasWeak == Init /\ [][Next]_x /\ WF_x(Copy)
Live == []<>(x = 0)
====
