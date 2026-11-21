---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Init == x = 0
Inv == {<<a,b>> \in {[i \in 1..2 |-> i]}: TRUE} # {}
Next == x' = x
====
