---- MODULE M ----
EXTENDS Integers, TLC, Sequences, FiniteSets
CONSTANT u, typed_a
ASSUME PrintT([z |-> 1, a |-> 2] @@ [b |-> 3, a |-> 4])
====
