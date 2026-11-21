---- MODULE M ----
EXTENDS Integers, TLC, Randomization, FiniteSets
Test == PrintT(LET z == RandomSubset(2, 1..20) IN z)
ASSUME Test
====
