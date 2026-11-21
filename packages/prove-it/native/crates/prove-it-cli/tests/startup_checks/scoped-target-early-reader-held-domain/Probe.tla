---- MODULE Probe ----
EXTENDS Naturals, FiniteSets, TLC
A == 1 + 1
Before == [i \in SUBSET {1} |-> A]
Mid == DOMAIN Before
K == 0
ASSUME PrintT(<<Before, A, K>>)
====
