---- MODULE Probe ----
EXTENDS Naturals, FiniteSets, TLC
A == 1 + 1
Before == {v \in [{1} -> {1, 2}] : A = 9}
K == 0
ASSUME PrintT(<<Before, A, K>>)
====
