---- MODULE K ----
EXTENDS Naturals
(* --algorithm foo
variable x = 0;
begin
  L: x := "q;
end algorithm *)
\* BEGIN TRANSLATION (chksum(pcal) = "4442b930" /\ chksum(tla) = "f3b88fe9")
VARIABLES pc2, x2

vars == << pc, x >>

Init == (* Global variables *)
        /\ x = 0
        /\ pc = "L"

L == /\ pc = "L"
     /\ x' = x + 1
     /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == L
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION
====
