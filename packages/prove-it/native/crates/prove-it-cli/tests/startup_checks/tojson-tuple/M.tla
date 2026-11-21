---- MODULE M ----
EXTENDS Integers, TLC, Json
VARIABLE x
Init == x = 0 /\ PrintT(ToJson(<<1, TRUE, "a">>))
Next == x' = x
====
