---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC, Randomization
Test == PrintT(RandomSubset(1, {PrintT(3), 2}))
ASSUME Test
====
