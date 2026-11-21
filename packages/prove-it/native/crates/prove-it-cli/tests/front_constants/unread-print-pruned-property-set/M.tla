---- MODULE M ----
EXTENDS Integers, TLC
D == PrintT(0) /\ FALSE /\ TLCSet("-Dbar", 3)
ASSUME PrintT(TLCGet("-Dbar"))
VARIABLE x
Init == x = 0
Next == x' = x
====
