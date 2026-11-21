---- MODULE M ----
EXTENDS Integers, TLC, Randomization
Test == PrintT(LET z == RandomSubset(2, 1..20) IN z) /\ 1 \div 0 = 1
ASSUME Test
====
