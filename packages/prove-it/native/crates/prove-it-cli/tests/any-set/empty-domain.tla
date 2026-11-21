---- MODULE M ----
EXTENDS TLC, FiniteSets
ASSUME IsFiniteSet([{} -> Any]) /\ Cardinality([{} -> Any]) = 1
====
