---- MODULE ShareInstance ----
EXTENDS Naturals
VARIABLES c
vars == <<c>>
S == {1, 2}
I == INSTANCE Inner WITH K <- 1
Init == c = [p \in 1..3 |-> 0]
Next == \E self \in S : I!P(self) \/ I!P(self + 1)
Spec == Init /\ [][Next]_vars /\ \A self \in {1} : WF_vars(I!a(self))
Prop == []<>(c[1] # 0)
Always == TRUE
====
