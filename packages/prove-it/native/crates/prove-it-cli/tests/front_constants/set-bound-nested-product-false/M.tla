---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
ASSUME Cardinality({p \in ({q \in (1..1001) \X (1..1000) : TRUE} \X {0}) : FALSE}) = 0
====
