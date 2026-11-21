---- MODULE M ----
EXTENDS Integers, TLC, Json
VARIABLE x
Init == x = 0 /\ PrintT(ToJson([a |-> 1]))
Next == x' = x
====
