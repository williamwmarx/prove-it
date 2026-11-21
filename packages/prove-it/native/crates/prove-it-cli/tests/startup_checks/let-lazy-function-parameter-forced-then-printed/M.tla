---- MODULE M ----
EXTENDS Integers, TLC
Op(c) == PrintT(c) /\ PrintT({c})
ASSUME LET C == [s \in SUBSET {1} |-> Print(<<"L", s>>, 0)] IN Op(C) /\ PrintT(C)
====
