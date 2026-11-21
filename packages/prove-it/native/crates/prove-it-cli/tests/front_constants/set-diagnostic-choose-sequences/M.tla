---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE x
Init == x = 0
Next == UNCHANGED x
ASSUME PrintT(CHOOSE e \in Seq({1}) : TRUE)
====
