---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
Bad(v) == IF PrintT(v) THEN Cardinality({y \in {z \in <<v>> : TRUE} : TRUE}) = 0 ELSE TRUE
ASSUME Bad(1)
====
