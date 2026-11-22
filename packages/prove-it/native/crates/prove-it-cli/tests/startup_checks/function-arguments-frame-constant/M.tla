---- MODULE M ----
EXTENDS Integers
VARIABLE x
C == [i \in 0..2, j \in 1..2 |-> i][1, 1 \div 0]
Init == x = C
Next == UNCHANGED x
====
