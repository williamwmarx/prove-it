---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE x
ASSUME PrintT((Int :> 1)[Int])
Init == x = 0
Next == UNCHANGED x
====
