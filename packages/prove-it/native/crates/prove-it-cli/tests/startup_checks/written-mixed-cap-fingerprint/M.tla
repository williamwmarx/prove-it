---- MODULE M ----
EXTENDS Integers, FiniteSets, TLC
VARIABLE x
Init == x = 0
Next == x' = Cardinality({1, "a"} \cap {x, 1})
====
