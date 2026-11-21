---- MODULE M ----
EXTENDS Integers, TLC, Json
VARIABLE x
Init == x = 0 /\ PrintT(ToJson((TRUE :> 2)))
Next == x' = x
====
