---- MODULE M ----
EXTENDS Integers, TLC, Json
VARIABLE x
Init == x = 0 /\ PrintT(ToJson(<<>>))
Next == x' = x
====
