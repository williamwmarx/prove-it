---- MODULE PcalModel ----
EXTENDS Naturals
CONSTANTS Procs, Leader
(* --algorithm PcalModel
fair process P \in Procs
variable c = 0;
begin
  a: while self # Leader \/ c < 2 do
       c := (c + 1) % 3;
     end while;
end process
end algorithm *)
\* BEGIN TRANSLATION
VARIABLES pc, c

vars == << pc, c >>

ProcSet == (Procs)

Init == (* Process P *)
        /\ c = [self \in Procs |-> 0]
        /\ pc = [self \in ProcSet |-> "a"]

a(self) == /\ pc[self] = "a"
           /\ IF self # Leader \/ c[self] < 2
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
        /\ \A self \in Procs : WF_vars(P(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
Always == TRUE
Live == <>(pc[Leader] = "Done")
Never == <>(\A p \in Procs : pc[p] = "Done")
====
