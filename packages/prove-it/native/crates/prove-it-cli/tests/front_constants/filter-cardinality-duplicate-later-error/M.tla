---- MODULE M ----
EXTENDS Integers, FiniteSets, TLC
VARIABLE n
Init == n = 0
Next == n' = (IF Cardinality({x \in ({x \in SUBSET {1} : TRUE} \cup {x \in SUBSET {1} : TRUE}) : (x = {}) \/ (x = {1})}) = 2 THEN 1 \div 0 ELSE 0)
====
