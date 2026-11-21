---- MODULE M ----
EXTENDS Integers, FiniteSets, TLC
S == {RandomElement(1..9), 70}
ASSUME PrintT(S) /\ PrintT(S \cup {1}) /\ Cardinality(S) = 2
====
