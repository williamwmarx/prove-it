---- MODULE M ----
EXTENDS Integers
ASSUME [i \in 0..2, j \in 1..2 |-> i][1, 1 \div 0] = 0
====
