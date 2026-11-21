---- MODULE M ----
EXTENDS Integers, TLC, FiniteSets
S == (SUBSET {1}) \cap (SUBSET {1,2})
ASSUME IF Cardinality(S) >= 0 THEN (IF PrintT(S) THEN S + 1 ELSE 0) ELSE 0
====
