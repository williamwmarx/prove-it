---- MODULE M ----
EXTENDS Naturals, TLC, Json
VARIABLE x
Init == x = 0 /\ PrintT(ToJson(<<1,2>>))
Next == x' = x
====
