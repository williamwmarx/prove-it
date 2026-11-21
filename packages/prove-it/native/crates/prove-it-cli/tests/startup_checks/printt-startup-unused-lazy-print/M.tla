---- MODULE M ----
EXTENDS Integers, Sequences, TLC
VARIABLE x
Bad == PrintT({y \in Nat : y = 1})
Init == x = 0
Next == x' = x
====
