---- MODULE M ----
EXTENDS Integers, FiniteSets, Sequences, TLC
VARIABLE x
Bad == PrintT(Int < -3)
ASSUME Bad
Init == x = 0
Next == UNCHANGED x
====
