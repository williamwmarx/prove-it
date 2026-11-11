---- MODULE ShareRing ----
EXTENDS Naturals
CONSTANT N
VARIABLES tok, pc
vars == <<tok, pc>>
ProcSet == 1..N
Init == /\ tok = [p \in ProcSet |-> 0]
        /\ pc = [self \in ProcSet |-> "work"]
Bump(p) == /\ pc[p] = "work"
           /\ tok' = [tok EXCEPT ![p] = (tok[p] + 1) % 2]
           /\ pc' = pc
work(self) == Bump(self)
help(self) == work((self % N) + 1)
proc(self) == work(self) \/ help(self)
Next == (\E self \in ProcSet: proc(self))
Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in ProcSet : WF_vars(Bump(self))
Live == []<>(tok[1] = 1)
Always == TRUE
====
