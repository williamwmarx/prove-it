---- MODULE M ----
EXTENDS Integers, Sequences, TLC
ASSUME PrintT(Append([i \in Nat |-> i],1))
====
