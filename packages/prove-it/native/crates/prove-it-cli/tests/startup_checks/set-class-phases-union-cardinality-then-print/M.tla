---- MODULE M ----
EXTENDS Integers, TLC, FiniteSets
S == UNION (SUBSET {{1}})
ASSUME IF Cardinality(S) >= 0 THEN (IF PrintT(S) THEN S + 1 ELSE 0) ELSE 0
====
