---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
ASSUME TLCSet(1, 0)
Init == x = 0
Next == \E v \in {TLCGet(1)} : x < 3 /\ x' = x + 1 /\ TLCSet(1, x + 10) /\ PrintT(<<x, v>>)
====
