---- MODULE PcalSet ----
EXTENDS Naturals
CONSTANT Procs
VARIABLES pc, c

vars == << pc, c >>

ProcSet == (Procs)

Init == (* Process P *)
        /\ c = [self \in Procs |-> 0]
        /\ pc = [self \in ProcSet |-> "a"]

a(self) == /\ pc[self] = "a"
           /\ IF self # 1 \/ c[self] < 2
                 THEN /\ c' = [c EXCEPT ![self] = (c[self] + 1) % 3]
                      /\ pc' = [pc EXCEPT ![self] = "a"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ c' = c

P(self) == a(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Procs: P(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in ProcSet : WF_vars(P(self))

Always == TRUE
Live == <>(pc[1] = "Done")
Never == <>(\A p \in Procs : pc[p] = "Done")
====
