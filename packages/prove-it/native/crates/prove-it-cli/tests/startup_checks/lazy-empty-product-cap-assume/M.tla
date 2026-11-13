---- MODULE M ----
EXTENDS Integers, FiniteSets, TLC
VARIABLE x
ASSUME PrintT((Int \X {}) \cap {"a"})
Init == x = 0
Next == x' = x
====
