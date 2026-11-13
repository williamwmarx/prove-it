---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Init == x = (<<1>> \in [a : {1}])
Next == x' = x
====
