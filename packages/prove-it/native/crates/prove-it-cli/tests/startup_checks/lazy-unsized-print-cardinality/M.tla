---- MODULE M ----
EXTENDS Integers, FiniteSets, TLC
VARIABLE x
Init == x = PrintT(Cardinality({[a : Int, b : {}]}))
Inv == x = TRUE
Next == x' = x
====
