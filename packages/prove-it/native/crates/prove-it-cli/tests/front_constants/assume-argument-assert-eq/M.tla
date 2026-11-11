---- MODULE M ----
EXTENDS Naturals, TLC, TLCExt, Sequences, FiniteSets
VARIABLE x
Twice(a) == <<a, a>>
Once(a) == <<a>>
Thrice(a) == a /\ a /\ a
Eq2(a) == a = a
Q(a) == \A i \in 1..2 : a = a
LetA(a) == LET z == a IN <<z, z>>
Inner(p, q) == <<q, p>>
Outer(a) == Inner(a, a)
MyEq(a, b) == AssertEq(a, b)
Cnt == TLCGet(1)
ASSUME Twice(AssertEq(1, 2)) \/ TRUE
Init == x = 0
Next == x' = (x + 1) % 2
Spec == Init /\ [][Next]_x

====
