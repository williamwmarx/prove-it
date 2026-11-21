---- MODULE M ----
EXTENDS Integers, Sequences, TLC
VARIABLE x
Bad == PrintT({1, 2})
ASSUME Bad
Init == x = 0
Next == UNCHANGED x
====
