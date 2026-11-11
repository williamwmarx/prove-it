---- MODULE PInEnumRcdEmptyWrap ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {}
Init == x = [a |-> 0]
A == x' \in [a : ({})]
B == x' = [a |-> 0]
E == x' = [a |-> 2]
Next == /\ (A \/ B \/ E)
Copy == x' \in [a : ({})]
Weak == Init /\ [][Next]_x /\ WF_x(A)
AliasWeak == Init /\ [][Next]_x /\ WF_x(Copy)
Live == []<>(x = [a |-> 0])
====
