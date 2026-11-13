---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE x
Init == x = (<<1>> \in [Nat -> {1}])
Next == x' = x
====
