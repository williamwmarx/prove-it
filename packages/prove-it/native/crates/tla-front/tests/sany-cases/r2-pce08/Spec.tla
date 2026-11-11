---- MODULE Spec ----
EXTENDS Naturals
(* --algorithm foo
variable x = 0;
begin
  A: x := "abc;
  B: while x < 3 do
    x := x + 1;
  end while;
end algorithm *)
\* BEGIN TRANSLATION (chksum(pcal) = "2f25bced" /\ chksum(tla) = "47019b77")
VARIABLES pc, x

vars == << pc, x >>

Init == (* Global variables *)
        /\ x = 0
        /\ pc = "A"

A == /\ pc = "A"
     /\ x' = x + 1
     /\ pc' = "B"

B == /\ pc = "B"
     /\ IF x < 3
           THEN /\ x' = x + 1
                /\ pc' = "B"
           ELSE /\ pc' = "Done"
                /\ x' = x

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == A \/ B
           \/ Terminating

Bad == Undef
Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION
====
