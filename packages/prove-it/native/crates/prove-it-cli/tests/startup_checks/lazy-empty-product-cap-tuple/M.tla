---- MODULE M ----
EXTENDS Integers, FiniteSets, TLC
VARIABLE x
Init == x = Cardinality((Int \X {}) \cap {<<1, 2>>})
Next == x' = x
====
