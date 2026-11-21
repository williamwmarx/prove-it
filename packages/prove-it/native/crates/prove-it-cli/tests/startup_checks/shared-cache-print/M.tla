---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
G(R, D) == Cardinality(D) >= 0 /\ PrintT(D) /\ (1 \in R)
F(R) == LET S == [{1} -> {}] IN G(R, S \ R)
ASSUME F({1})
====
