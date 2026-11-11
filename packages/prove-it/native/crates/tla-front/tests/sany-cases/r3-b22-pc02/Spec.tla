---- MODULE Spec ----
EXTENDS A
VARIABLE x
(* --algorithm bar
variable z = 0;
begin
  z := 1;
end algorithm *)
\* BEGIN TRANSLATION (chksum(pcal) = "12345678" /\ chksum(tla) = "87654321")
VARIABLES pc, z
vars == << pc, z >>
Init == z = 0 /\ pc = "Lbl_1"
\* END TRANSLATION

====
