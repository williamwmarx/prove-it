---- MODULE M ----
EXTENDS Naturals, TLC, Json
VARIABLE x
Init == x = 0 /\ PrintT(ToJson({1} :> x))
Next == UNCHANGED x /\ PrintT(ToJson((x' :> {x}) :> 2))
====
