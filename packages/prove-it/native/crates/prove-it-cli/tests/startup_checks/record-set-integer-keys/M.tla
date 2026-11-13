---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Init == x = ([i \in {1} |-> 1] \in [a : {1}])
Next == x' = x
====
