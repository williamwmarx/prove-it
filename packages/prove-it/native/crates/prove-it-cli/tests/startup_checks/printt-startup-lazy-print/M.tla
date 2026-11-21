---- MODULE M ----
EXTENDS Integers, Sequences, TLC
VARIABLE x
Bad == PrintT({y \in Nat : y = 1})
ASSUME Bad
Init == x = 0
Next == UNCHANGED x
====
