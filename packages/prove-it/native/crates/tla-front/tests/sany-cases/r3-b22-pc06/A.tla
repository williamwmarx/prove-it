---- MODULE A ----
(* --algorithm foo
variable y = 0;
begin
  y := 1;
end algorithm *)
\* BEGIN TRANSLATION (chksum(pcal) = "12345678" /\ chksum(tla) = "87654321")
VARIABLES pc, y
vars == << pc, y >>
Init == y = 0 /\ pc = "Lbl_1"
\* END TRANSLATION
Q == 1
Q == 2
====
