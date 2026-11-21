---- MODULE M ----
EXTENDS Integers, TLC, Sequences, FiniteSets
CONSTANT u, typed_a
ASSUME PrintT((1 :> 1) @@ ((2 :> 3) \ ({9})))
====
