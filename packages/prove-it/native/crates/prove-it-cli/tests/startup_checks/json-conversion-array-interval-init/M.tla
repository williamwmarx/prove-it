---- MODULE M ----
EXTENDS Integers,TLC,Json
VARIABLE x
Init == x = 0 /\ PrintT(ToJsonArray(1..3))
Next == x' = x
====
