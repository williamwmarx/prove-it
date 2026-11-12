---- MODULE C ----
(* --algorithm foo
variable w = 0;
begin
  w := 1;
end algorithm *)
\* BEGIN TRANSLATION (chksum(pcal) = "12345678" /\ chksum(tla) = "87654321")
VARIABLES pc, w
vars == << pc, w >>
Init == w = 0 /\ pc = "Lbl_1"
\* END TRANSLATION

====
