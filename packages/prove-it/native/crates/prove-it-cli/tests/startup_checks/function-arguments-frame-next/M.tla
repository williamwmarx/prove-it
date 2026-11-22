---- MODULE M ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = x + [i \in 0..2, j \in 1..2 |-> i][1 \div x, 1]
====
