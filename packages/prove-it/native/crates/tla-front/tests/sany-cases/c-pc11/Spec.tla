---- MODULE Spec ----
EXTENDS Naturals
(* --algorithm foo
variable x = 0;
begin
  x := "abc;
end algorithm *)
\* BEGIN TRANSLATION (chksum(pcal) = "5cf55c2d" /\ chksum(tla) = "acb3d344")
VARIABLES pc, x

Bad == Undefined
vars == << pc, x >>

Init == (* Global variables *)
        /\ x = 0
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ x' = x + 1
         /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION
====
