---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE x
Init == x = IsFiniteSet([Int -> {1}] \ {})
Inv == x = TRUE
Next == x' = x
====
