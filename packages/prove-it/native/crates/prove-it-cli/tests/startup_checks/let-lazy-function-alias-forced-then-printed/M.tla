---- MODULE M ----
EXTENDS Integers, TLC
ASSUME LET C == [s \in SUBSET {1} |-> Print(<<"L", s>>, 0)] IN LET E == C IN PrintT(C) /\ PrintT({E}) /\ PrintT(C)
====
