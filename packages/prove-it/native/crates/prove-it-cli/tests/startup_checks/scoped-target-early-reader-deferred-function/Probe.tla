---- MODULE Probe ----
EXTENDS Integers, Sequences, FiniteSets, TLC
A == 1+1
Before == [i \in SUBSET {1} |-> A]
K == 0
L == 0
ASSUME PrintT(<<Before, A>>)
====
