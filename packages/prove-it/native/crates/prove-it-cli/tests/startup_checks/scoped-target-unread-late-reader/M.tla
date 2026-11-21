---- MODULE M ----
EXTENDS Naturals, TLC
A == 1 + 1
Before == A
K == 0
Middle == A
L == 0
After == {n \in 1..A : n > Middle}
Ignore(v) == TRUE
ASSUME Ignore(Before) /\ Before = 9 /\ K = 2 /\ L = 2
====
