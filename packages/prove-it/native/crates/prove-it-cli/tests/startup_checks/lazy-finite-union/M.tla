---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE x
Init == x = IsFiniteSet([a : Int, b : {1}] \cup {})
Inv == x = FALSE
Next == x' = x
====
