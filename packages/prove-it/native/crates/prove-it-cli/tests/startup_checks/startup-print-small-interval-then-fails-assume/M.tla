---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC, Randomization
Test == PrintT(1..1000001) /\ 1 \div 0 = 1
ASSUME Test
====
