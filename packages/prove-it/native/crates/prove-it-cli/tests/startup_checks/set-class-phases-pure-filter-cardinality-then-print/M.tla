---- MODULE M ----
EXTENDS Integers, TLC, FiniteSets
S == {k \in SUBSET {1} : TRUE}
ASSUME IF Cardinality(S) >= 0 THEN (IF PrintT(S) THEN S + 1 ELSE 0) ELSE 0
====
