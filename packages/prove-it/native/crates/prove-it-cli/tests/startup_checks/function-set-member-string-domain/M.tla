---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE x
Init == x = ([a |-> 1] \in [STRING -> Nat])
Next == x' = x
====
