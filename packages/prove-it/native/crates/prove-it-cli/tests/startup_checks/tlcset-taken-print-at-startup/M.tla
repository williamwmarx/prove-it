---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE x
D == (Len(<<1>>) = 2) \/ (PrintT("x") /\ TLCSet(1, 2))
Init == x = 0
Next == x < 1 /\ x' = x + 1
====
