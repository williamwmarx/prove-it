---- MODULE ShareAction ----
EXTENDS Naturals
VARIABLES c
vars == <<c>>
S == {1, 2}
Init == c = [p \in 1..3 |-> 0]
a(p) == c' = [c EXCEPT ![p] = (c[p] + 1) % 3]
P(p) == a(p)
Next == \E self \in S : P(self) \/ P(self + 1)
Spec == Init /\ [][Next]_vars /\ \A self \in {1} : WF_vars(a(self))
Prop == []<>(c[1] # 0)
Always == TRUE
====
