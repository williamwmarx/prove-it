---- MODULE Probe ----
EXTENDS Integers, Sequences, FiniteSets, TLC, TLCExt, Randomization, Bags
D == RandomElement({0, 2})
Test == (D = 1) /\ TLCSet(1, 2)
VARIABLE s
Init == s = Test
Next == UNCHANGED s
Inv == ~s
====
