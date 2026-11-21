---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE x
D == (Len(<<1>>) = 1) \/ (PrintT("x") /\ TLCSet(1, 2))
Init == x = 0
Next == x < 2 /\ x' = x + 1
Inv == D /\ x < 2
====
