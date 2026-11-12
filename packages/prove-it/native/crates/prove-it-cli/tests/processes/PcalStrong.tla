---- MODULE PcalStrong ----
EXTENDS Naturals
(* --algorithm PcalStrong
variable x = 0;
fair+ process P \in 1..2
begin
  a: if self = 1 then
       await x = 0;
     else
       b: while TRUE do
            x := 1 - x;
          end while;
     end if;
end process
end algorithm *)
\* BEGIN TRANSLATION
VARIABLES pc, x

vars == << pc, x >>

ProcSet == (1..2)

Init == (* Global variables *)
        /\ x = 0
        /\ pc = [self \in ProcSet |-> "a"]

a(self) == /\ pc[self] = "a"
           /\ IF self = 1
                 THEN /\ x = 0
                      /\ pc' = [pc EXCEPT ![self] = "Done"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "b"]
           /\ x' = x

b(self) == /\ pc[self] = "b"
           /\ x' = 1 - x
           /\ pc' = [pc EXCEPT ![self] = "b"]

P(self) == a(self) \/ b(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..2: P(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..2 : SF_vars(P(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
Always == TRUE
Live == <>(pc[1] = "Done")
Never == <>(pc[2] = "Done")
====
