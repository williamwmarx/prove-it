---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC, Randomization
Test == PrintT("before") /\ TLCSet("exit", FALSE)
ASSUME Test
ASSUME Test
====
