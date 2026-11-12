---- MODULE PcalTwo ----
EXTENDS Naturals
(* --algorithm PcalTwo
fair process A \in {1, 2}
variable c = 0;
begin
  a: while self # 1 \/ c < 2 do
       c := (c + 1) % 3;
     end while;
end process
fair process B \in 3..4
variable d = 0;
begin
  b: while self # 3 \/ d < 2 do
       d := (d + 1) % 3;
     end while;
end process
end algorithm *)
\* BEGIN TRANSLATION
VARIABLES pc, c, d

vars == << pc, c, d >>

ProcSet == ({1, 2}) \cup (3..4)

Init == (* Process A *)
        /\ c = [self \in {1, 2} |-> 0]
        (* Process B *)
        /\ d = [self \in 3..4 |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self \in {1, 2} -> "a"
                                        [] self \in 3..4 -> "b"]

a(self) == /\ pc[self] = "a"
           /\ IF self # 1 \/ c[self] < 2
                 THEN /\ c' = [c EXCEPT ![self] = (c[self] + 1) % 3]
                      /\ pc' = [pc EXCEPT ![self] = "a"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ c' = c
           /\ d' = d

A(self) == a(self)

b(self) == /\ pc[self] = "b"
           /\ IF self # 3 \/ d[self] < 2
                 THEN /\ d' = [d EXCEPT ![self] = (d[self] + 1) % 3]
                      /\ pc' = [pc EXCEPT ![self] = "b"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ d' = d
           /\ c' = c

B(self) == b(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in {1, 2}: A(self))
           \/ (\E self \in 3..4: B(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {1, 2} : WF_vars(A(self))
        /\ \A self \in 3..4 : WF_vars(B(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
Always == TRUE
Live == <>(pc[1] = "Done") /\ <>(pc[3] = "Done")
Never == <>(\A p \in ProcSet : pc[p] = "Done")
====
