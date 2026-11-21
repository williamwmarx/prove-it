---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE x
Init == x = 0
Next == UNCHANGED x
ASSUME PrintT([b |-> 2, a |-> 1] \subseteq Print("right",{}))
====
