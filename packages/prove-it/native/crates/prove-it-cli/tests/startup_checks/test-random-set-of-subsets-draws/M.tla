---- MODULE M ----
EXTENDS Randomization, FiniteSets, Naturals, TLC
ASSUME PrintT(TestRandomSetOfSubsets(3, 2, 1..4))
ASSUME PrintT(TestRandomSetOfSubsets(3, 2, 1..4)[2])
ASSUME DOMAIN TestRandomSetOfSubsets(3, 2, 1..4) = 1..5
ASSUME PrintT(RandomElement(1..1000))
====
