---- MODULE M ----
EXTENDS Integers, TLC, Sequences, FiniteSets
CONSTANT u, typed_a
ASSUME PrintT((1 :> 1) @@ (({9}) \cup (2 :> 3)))
====
