---- MODULE M ----
EXTENDS Integers, Sequences, TLC
ASSUME PrintT(Tail([i \in Nat |-> Print(i,i)]))
====
