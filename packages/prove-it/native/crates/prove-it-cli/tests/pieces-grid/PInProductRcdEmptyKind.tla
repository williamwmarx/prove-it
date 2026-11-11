---- MODULE PInProductRcdEmptyKind ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {}
Init == x = [a |-> <<0, 1>>]
A == x' \in [a : ({} \X {1})]
B == x' = [a |-> <<0, 1>>]
E == x' = [a |-> <<2, 1>>]
Next == /\ (A \/ B \/ E)
Copy == x' \in [a : ({} \X {1})]
Weak == Init /\ [][Next]_x /\ WF_x(A)
AliasWeak == Init /\ [][Next]_x /\ WF_x(Copy)
Live == []<>(x = [a |-> <<0, 1>>])
====
