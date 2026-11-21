---- MODULE Probe ----
EXTENDS Naturals, FiniteSets, TLC
A == 1 + 1
Before == {v \in SUBSET {1} : A = 9}
Mid == Before \subseteq {}
K == 0
ASSUME PrintT(<<Before, A, K>>)
====
