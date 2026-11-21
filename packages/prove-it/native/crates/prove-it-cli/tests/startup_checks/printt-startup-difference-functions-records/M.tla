---- MODULE M ----
EXTENDS Integers, Sequences, TLC
VARIABLE x
D == PrintT([{1} -> {2, 3}] \ {[a |-> 1], [a |-> 2]})
ASSUME D
Init == x = 0
Next == x' = x
====
