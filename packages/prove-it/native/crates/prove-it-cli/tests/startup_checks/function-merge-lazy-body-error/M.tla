---- MODULE M ----
EXTENDS Integers, TLC, Sequences, FiniteSets
CONSTANT u, typed_a
ASSUME PrintT(([k \in (SUBSET {1}) |-> Print("body-left", k)]) @@ (Print("other", FALSE)))
====
