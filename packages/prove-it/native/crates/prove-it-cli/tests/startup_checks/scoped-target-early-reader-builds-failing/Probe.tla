---- MODULE Probe ----
EXTENDS Integers, Sequences, FiniteSets, TLC
A == 1+1
Before == [v \in {A} |-> 1 \div 0]
K == 0
ASSUME PrintT(<<A, Before>>)
====
