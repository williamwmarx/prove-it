---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Init == x = (<<>> \in [a : {1}])
Next == x' = x
====
