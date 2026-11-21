---- MODULE M ----
EXTENDS Integers
VARIABLE x
Init == x = [i \in 0..2, j \in 1..2 |-> i][1, 1 \div 0]
Next == UNCHANGED x
====
