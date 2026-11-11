---- MODULE M ----
EXTENDS Naturals, Sequences
VARIABLE x
Init == x = 0
Next == UNCHANGED x
Inv == <<>> \notin [{1} -> {z \in {0, 1} : [c |-> 1] \notin [a : {1 \div (z - 1)}]}]
====