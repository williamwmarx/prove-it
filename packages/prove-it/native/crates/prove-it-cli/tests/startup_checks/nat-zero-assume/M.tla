---- MODULE M ----
EXTENDS Integers, FiniteSets, Sequences, TLC
VARIABLE x
Bad == PrintT((Nat)[0])
ASSUME Bad
Init == x = 0
Next == UNCHANGED x
====
