---- MODULE Probe ----
EXTENDS Naturals, FiniteSets, TLC
A == 1 + 1
Before == {v \in SUBSET {1} : A = 9}
Mid == LET L == Before IN L
K == 0
ASSUME PrintT(<<Before, A, K>>)
====
