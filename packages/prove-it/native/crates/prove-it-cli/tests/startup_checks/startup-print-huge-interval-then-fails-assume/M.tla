---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC, Randomization
Test == PrintT(1..2147483647) /\ 1 \div 0 = 1
ASSUME Test
====
