---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Init == x = (<<>> \notin [a : {1}, b : {2}])
Next == x' = x
====
