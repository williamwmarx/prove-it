---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE s
Init == s = 0
Next == s' = Cardinality({IF x = 1000001 THEN 1 \div 0 ELSE 0 : x \in 1..1000001})
====
