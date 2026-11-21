---- MODULE Probe ----
EXTENDS Integers, Sequences, FiniteSets, TLC, TLCExt, Randomization, Bags
Test == (RandomSubset(1, {0, 2}) = {1}) /\ TLCSet(1, 2)
VARIABLE s
Init == s = Test
Next == UNCHANGED s
Inv == ~s
====
