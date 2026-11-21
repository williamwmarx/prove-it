---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
Test == PrintT(7 \ {1})
ASSUME Test
====
