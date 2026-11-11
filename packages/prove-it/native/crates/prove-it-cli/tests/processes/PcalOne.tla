---- MODULE PcalOne ----
EXTENDS Naturals
CONSTANT N
(* --algorithm PcalOne
fair process P \in 1..N
variable c = 0;
begin
  a: while self # 1 \/ c < 2 do
       c := (c + 1) % 3;
     end while;
end process
end algorithm *)
\* BEGIN TRANSLATION
VARIABLES pc, c

vars == << pc, c >>

ProcSet == (1..N)

Init == (* Process P *)
        /\ c = [self \in 1..N |-> 0]
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

Next == (\E self \in 1..N: P(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..N : WF_vars(P(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
Always == TRUE
Live == <>(pc[1] = "Done")
Never == <>(\A p \in 1..N : pc[p] = "Done")
====
