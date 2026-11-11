---- MODULE ShareInstanceArg ----
EXTENDS Naturals
VARIABLES c
vars == <<c>>
S == {1, 2}
J(k) == INSTANCE Inner WITH K <- k
Init == c = [p \in 1..3 |-> 0]
Next == \E self \in S : J(1)!P(self) \/ J(1)!P(self + 1)
Spec == Init /\ [][Next]_vars /\ \A self \in {1} : WF_vars(J(1)!a(self))
Prop == []<>(c[1] # 0)
Always == TRUE
====
