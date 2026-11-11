---- MODULE GSCallDefSame ----
EXTENDS Naturals
CONSTANTS N, Procs
VARIABLES pc, c
vars == <<pc, c>>
D == 1..N+1
Ids == 1..N
Init == pc = [p \in D |-> "a"] /\ c = [p \in D |-> 0]
a(self) == /\ pc[self] = "a"
           /\ IF self # 1 \/ c[self] < 2
                 THEN /\ c' = [c EXCEPT ![self] = (c[self] + 1) % 3]
                      /\ pc' = pc
                 ELSE /\ pc' = [pc EXCEPT ![self] = "b"]
                      /\ c' = c
b(self) == pc[self] = "b" /\ pc' = [pc EXCEPT ![self] = "Done"] /\ c' = c
P(self) == a(self) \/ b(self)
CopyP(self) == P(self) /\ TRUE
CopyA(self) == a(self) /\ TRUE
CopyB(self) == b(self) /\ TRUE
Terminating == (\A p \in D : pc[p] = "Done") /\ UNCHANGED vars
Next == (\E self \in Ids : P(self)) \/ Terminating
Weak == Init /\ [][Next]_vars /\ \A self \in 1..N : SF_vars(P(self))
AliasWeak == Init /\ [][Next]_vars /\ \A self \in 1..N : SF_vars(CopyP(self))
Always == TRUE
Live == <>(pc[1] = "Done")
====
