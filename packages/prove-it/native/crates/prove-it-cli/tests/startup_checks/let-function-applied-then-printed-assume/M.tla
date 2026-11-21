---- MODULE M ----
EXTENDS Integers, TLC
ASSUME PrintT(LET C[s \in SUBSET {1}] == Print(<<"L", s>>, 0) IN C[{}] = 0 /\ PrintT(C) /\ PrintT(C))
====
