---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Init == x = ({<<a,b>> \in {[i \in 1..2 |-> i]}: TRUE} # {})
Next == x' = x
====
