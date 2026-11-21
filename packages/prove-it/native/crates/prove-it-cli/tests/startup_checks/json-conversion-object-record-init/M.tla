---- MODULE M ----
EXTENDS Integers,TLC,Json
VARIABLE x
Init == x = 0 /\ PrintT(ToJsonObject([b |-> FALSE,a |-> TRUE]))
Next == x' = x
====
