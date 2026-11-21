---- MODULE M ----
EXTENDS Naturals,TLC
ASSUME PrintT(([ [k \in 2147483647..2147483647 |-> k] EXCEPT ![0] = 0])[2147483647])
====
