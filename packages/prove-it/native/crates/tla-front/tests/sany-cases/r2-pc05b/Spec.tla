---- MODULE Spec ----
EXTENDS Naturals
(* PlusCal options (-wrongopt) *)
(* --algorithm foo
variable x = 0;
begin
  A: x := x + 1;
end algorithm *)
\* BEGIN TRANSLATION (chksum(pcal) = "a00bf1f8" /\ chksum(tla) = "f2a81d6a")
VARIABLES pc, x

vars == << pc, x >>

Init == (* Global variables *)
        /\ x = 0
        /\ pc = "A"

A == /\ pc = "A"
     /\ x' = x + 1
     /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == A
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION
====
