---- MODULE Probe ----
EXTENDS Integers, Sequences, FiniteSets, TLC
A == 1+1
Before == {v \in SUBSET {1}: A=9}
K == 0
L == 0
ASSUME PrintT(<<Before, A>>)
====
