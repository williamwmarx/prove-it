---- MODULE M ----
EXTENDS Integers, TLC, Sequences, FiniteSets
CONSTANT u, typed_a
ASSUME PrintT((({9}) \cup (<<>>)) @@ (1 :> 1))
====
