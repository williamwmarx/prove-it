---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE s
Init == s = 0
Next == s' = Cardinality({p \in (1..1001) \X (1..1000) : TRUE})
====
