---- MODULE Probe ----
EXTENDS Integers, Sequences, FiniteSets, TLC
A == IF RandomElement({1,2,3}) = 1 THEN 1 ELSE 1 \div 0
K == 0
L == 0
ASSUME PrintT(A)
====
