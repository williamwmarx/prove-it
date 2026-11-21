---- MODULE M ----
EXTENDS Integers, TLC, Json
VARIABLE x
Init == x = 0 /\ PrintT(ToJson([b |-> 1, a |-> 2]))
Next == x' = x
====
