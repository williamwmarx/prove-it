---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
S(k) == TLCSet(k, 2)
D == (1 = 1) /\ S(1)
ASSUME D /\ PrintT(TLCGet(1))
Init == x = 0
Next == x' = x
====
