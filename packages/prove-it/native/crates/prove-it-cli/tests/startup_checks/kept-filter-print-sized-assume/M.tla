---- MODULE M ----
EXTENDS Integers, FiniteSets, TLC
S == {x \in 1..3 : PrintT(x)}
ASSUME Cardinality(S) > 0
====
