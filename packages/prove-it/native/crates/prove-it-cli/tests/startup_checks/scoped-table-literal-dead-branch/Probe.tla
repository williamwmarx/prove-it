---- MODULE Probe ----
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANT C
A == 2
Ignore(x) == TRUE
ASSUME IF TRUE THEN TRUE ELSE C = 7
====
