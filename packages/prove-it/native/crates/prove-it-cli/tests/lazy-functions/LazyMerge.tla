---- MODULE LazyMerge ----
EXTENDS Integers, Sequences, TLC
ASSUME PrintT("a" \o [x \in Nat |-> x])
====
