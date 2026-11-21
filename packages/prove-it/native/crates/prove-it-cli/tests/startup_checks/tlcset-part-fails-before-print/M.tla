---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE x
D == /\ {} = <<>>
     /\ PrintT(9)
     /\ TLCSet(1, 2)
Test == ({} \in 1..2) /\ PrintT(1) /\ TLCSet(1, 6)
Init == x = 0
Next == x < 1 /\ x' = x + 1
ASSUME PrintT(5) /\ Test
====
