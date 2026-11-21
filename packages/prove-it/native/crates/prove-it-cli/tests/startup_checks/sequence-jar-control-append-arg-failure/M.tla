---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE x
Init == x = 0
Next == x' = x
ASSUME Append(1, Head(<<>>)) = 0
====