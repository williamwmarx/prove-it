---- MODULE M ----
EXTENDS Integers, FiniteSets, TLC
VARIABLE x
Init == x = IsFiniteSet([a : Int, b : {}] \ {1})
Inv == x = TRUE
Next == x' = x
====
