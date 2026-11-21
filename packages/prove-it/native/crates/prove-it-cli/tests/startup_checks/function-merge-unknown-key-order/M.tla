---- MODULE M ----
EXTENDS Integers, TLC, Sequences, FiniteSets
CONSTANT u, typed_a
ASSUME PrintT((((1 :> 10) @@ (u :> 20)) :> 11) @@ (1 :> 22))
====
