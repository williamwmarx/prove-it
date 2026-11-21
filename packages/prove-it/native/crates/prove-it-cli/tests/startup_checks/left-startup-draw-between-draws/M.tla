---- MODULE M ----
EXTENDS Integers, TLC, Randomization, FiniteSets
A == PrintT(RandomElement(1..100))
Test == PrintT(LET z == RandomSubset(2, 1..20) IN <<z, Cardinality(z)>>)
Z == PrintT(RandomElement(1..100))
ASSUME Test
ASSUME PrintT(RandomElement(1..100))
====
