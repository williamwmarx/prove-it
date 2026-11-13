---- MODULE M ----
EXTENDS Integers, FiniteSets, TLC
VARIABLE x
Init == x = Cardinality(Int \X {})
Next == x' = x
====
