---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE x
Init == x = 0
Next == UNCHANGED x
ASSUME PrintT([n \in {1,2} |-> n] \subseteq {})
====
