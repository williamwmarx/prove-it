---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
ASSUME Cardinality({0 : x \in 1..1000000}) = 1 /\ Cardinality({x \in 1..1000001 : FALSE}) = 0 /\ Cardinality(1..1000001) = 1000001 /\ <<1,1>> \in {p \in (1..1001) \X (1..1000) : TRUE}
====
