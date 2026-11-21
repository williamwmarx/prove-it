---- MODULE M ----
EXTENDS Integers, TLC, Sequences, FiniteSets
CONSTANT u, typed_a
ASSUME PrintT((SUBSET {1}) @@ (1 :> 1))
====
