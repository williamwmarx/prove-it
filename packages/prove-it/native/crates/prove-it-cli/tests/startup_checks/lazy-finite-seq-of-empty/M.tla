---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE x
Init == x = IsFiniteSet(Seq({}) \ {})
Inv == x = TRUE
Next == x' = x
====
