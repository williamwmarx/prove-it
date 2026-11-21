---- MODULE M ----
EXTENDS Integers, Sequences, TLC
VARIABLE x
Bad == PrintT({1, TRUE})
Init == x = 0
Next == x' = x
====
