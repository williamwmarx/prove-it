---- MODULE M ----
EXTENDS Integers, Sequences, TLC
VARIABLE x
D == PrintT([a : {1, 2}] \ ({1} \cup {2}))
ASSUME D
Init == x = 0
Next == x' = x
====
