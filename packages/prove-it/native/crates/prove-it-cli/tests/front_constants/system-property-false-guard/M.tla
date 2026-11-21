---- MODULE M ----
EXTENDS Integers, TLC
S(k) == (k \div 1 = 1) /\ TLCSet("-Dbar", k)
D == S(4)
ASSUME PrintT(TLCGet("-Dbar"))
VARIABLE x
Init == x = 0
Next == x' = x
====
