---- MODULE M ----
EXTENDS Integers, FiniteSets, Sequences, TLC
VARIABLE x
ASSUME PrintT((([a : {1}, b : {1}] \cup {1}) \subseteq {})) \/ TRUE
Init == x = 0
Next == x' = x
====
