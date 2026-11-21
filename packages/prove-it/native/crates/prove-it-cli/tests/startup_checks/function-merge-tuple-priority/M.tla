---- MODULE M ----
EXTENDS Integers, TLC, Sequences, FiniteSets
CONSTANT u, typed_a
ASSUME PrintT(<<10, 20>> @@ ((2 :> 99) @@ (3 :> 30)))
====
