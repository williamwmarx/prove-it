---- MODULE M ----
EXTENDS Integers, TLC, Sequences
VARIABLE x
ASSUME PrintT({3, 1, 2, 1, 3})
Init == x = 0
Next == x' = x
====
