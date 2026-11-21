---- MODULE M ----
EXTENDS Integers, TLC
A == [b |-> 2, a |-> 1]
K == 0
L == 0
ASSUME PrintT(<<K, A, L>>)
====
