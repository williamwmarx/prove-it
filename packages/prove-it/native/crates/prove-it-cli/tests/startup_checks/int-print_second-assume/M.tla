---- MODULE M ----
EXTENDS Integers, FiniteSets, Sequences, TLC
VARIABLE x
Bad == Print("tag", 1 + Int)
ASSUME Bad
Init == x = 0
Next == UNCHANGED x
====
