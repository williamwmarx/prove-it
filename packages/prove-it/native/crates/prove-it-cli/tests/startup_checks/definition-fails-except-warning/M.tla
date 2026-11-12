---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
VARIABLE x
D == PrintT(Tail([<<>> EXCEPT ![1] = (1 :> 2)[2]]))
ASSUME D
Init == x = 0
Next == x' = x
====
