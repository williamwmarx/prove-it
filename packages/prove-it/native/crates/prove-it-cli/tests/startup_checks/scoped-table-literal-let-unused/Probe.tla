---- MODULE Probe ----
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANT C
A == 2
Ignore(x) == TRUE
ASSUME LET D == C IN TRUE
====
