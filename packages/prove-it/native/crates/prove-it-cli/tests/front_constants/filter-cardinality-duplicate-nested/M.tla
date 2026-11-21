---- MODULE M ----
EXTENDS Integers, FiniteSets, TLC
ASSUME Cardinality({y \in {x \in ({x \in SUBSET {1} : TRUE} \cup {x \in SUBSET {1} : TRUE}) : (x = {}) \/ (x = {1})} : TRUE}) = 2
====
