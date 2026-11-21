---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC, Randomization
Test == PrintT(RandomSubset(1, {Print(1, 1), 2}))
ASSUME Test
ASSUME Test
====
