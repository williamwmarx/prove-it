---- MODULE M ----
EXTENDS Integers, TLC, Sequences, FiniteSets
CONSTANT u, typed_a
ASSUME PrintT(({(({1, "s"} :> 42)), (({1} :> 1))}) @@ (1 :> 2))
====
