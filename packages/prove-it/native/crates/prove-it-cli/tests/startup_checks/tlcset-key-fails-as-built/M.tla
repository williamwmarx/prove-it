---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC, Randomization
Test == TLCSet(<<1 \div 0>>, PrintT(1)) /\ PrintT(2)
VARIABLE x
Init == x = 0 /\ Test
Next == x' = x
====
