---- MODULE M ----
EXTENDS Integers, FiniteSets, TLC
LETCard == LET S == {x \in SUBSET {1} : TRUE} IN Cardinality({x \in (S \cup S) : TRUE})
ASSUME PrintT(LETCard)
====
