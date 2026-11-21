---- MODULE Probe ----
EXTENDS Integers, Sequences, FiniteSets, TLC, TLCExt, Randomization, Bags
Test == (RandomElement(SUBSET {1, 2}) = {3}) /\ TLCSet(1, 2)
VARIABLE s
Init == s = Test
Next == UNCHANGED s
Inv == ~s
====
