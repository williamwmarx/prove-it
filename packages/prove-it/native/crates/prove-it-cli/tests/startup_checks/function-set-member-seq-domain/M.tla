---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE x
Init == x = (<<>> \in [Seq({1}) -> {}])
Next == x' = x
====
