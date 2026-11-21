---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
A == 1+1
Before == {v \in {w \in {1,2} : TRUE} : A = 9}
K == 0
L == 0
ASSUME PrintT(Before)
====
