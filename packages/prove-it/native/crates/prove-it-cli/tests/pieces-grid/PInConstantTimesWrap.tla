---- MODULE PInConstantTimesWrap ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {1, 3}
Init == x = <<0, 1>>
A == x' \in (C) \X {1}
B == x' = <<0, 1>>
E == x' = <<2, 1>>
Next == /\ (A \/ B \/ E)
Copy == x' \in (C) \X {1}
Weak == Init /\ [][Next]_x /\ WF_x(A)
AliasWeak == Init /\ [][Next]_x /\ WF_x(Copy)
Live == []<>(x = <<0, 1>>)
====
