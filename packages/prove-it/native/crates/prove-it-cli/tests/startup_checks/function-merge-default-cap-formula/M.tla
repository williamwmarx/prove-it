---- MODULE M ----
EXTENDS Integers, TLC, Sequences, FiniteSets
CONSTANT u, typed_a
ASSUME PrintT(({Nat \cap (2 :> 3)}) @@ (1 :> 1))
====
