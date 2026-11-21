---- MODULE M ----
EXTENDS Integers, TLC, Json
VARIABLE x
Init == x = 0 /\ PrintT(ToJson([i \in 1..2 |-> i]))
Next == x' = x
====
