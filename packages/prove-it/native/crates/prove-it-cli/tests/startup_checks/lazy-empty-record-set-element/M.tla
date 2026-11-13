---- MODULE M ----
EXTENDS Integers, FiniteSets, TLC
VARIABLE x
Init == x = Cardinality({[a : {}, b : Int]})
Next == x' = x
====
