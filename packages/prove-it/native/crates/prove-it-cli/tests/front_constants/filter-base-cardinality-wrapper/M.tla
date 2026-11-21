---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
ASSUME Cardinality({y \in {x \in <<3,1,2,1>> : TLCGet(0) = 0} : TRUE}) = 0
====
