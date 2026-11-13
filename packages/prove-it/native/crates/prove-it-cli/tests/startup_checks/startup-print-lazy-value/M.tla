---- MODULE M ----
EXTENDS Naturals, TLC
Test == Print(1, [i \in 1..3 |-> i])
ASSUME Test[1] = 1
====
