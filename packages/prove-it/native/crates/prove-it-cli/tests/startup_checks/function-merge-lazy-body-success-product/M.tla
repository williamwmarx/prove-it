---- MODULE M ----
EXTENDS Integers, TLC, Sequences, FiniteSets
CONSTANT u, typed_a
ASSUME PrintT(([k \in ({1} \X {2}) |-> Print("body-left", k)]) @@ ([k \in ({1} \X {2}) |-> Print("body-right", k)]))
====
