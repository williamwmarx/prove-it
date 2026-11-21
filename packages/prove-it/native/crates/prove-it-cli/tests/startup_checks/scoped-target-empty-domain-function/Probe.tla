---- MODULE Probe ----
EXTENDS Integers, TLC
A[i \in {v \in {}: TRUE}] == 1 \div 0
K == 0
L == 0
ASSUME PrintT(A)
====
