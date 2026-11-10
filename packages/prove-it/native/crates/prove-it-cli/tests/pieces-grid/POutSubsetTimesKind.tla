---- MODULE POutSubsetTimesKind ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {1, 3}
Init == x = <<{0}, 1>>
A == x' \in (SUBSET {1, 3}) \X {1}
B == x' = <<{0}, 1>>
E == x' = <<{2}, 1>>
Next == /\ (A \/ B \/ E)
Copy == x' = <<{0}, 1>>
Weak == Init /\ [][Next]_x /\ WF_x(B)
AliasWeak == Init /\ [][Next]_x /\ WF_x(Copy)
Live == []<>(x = <<{0}, 1>>)
====
