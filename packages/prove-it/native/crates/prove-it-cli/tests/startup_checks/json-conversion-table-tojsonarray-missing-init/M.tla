---- MODULE M ----
EXTENDS Integers,TLC,Json
VARIABLE x
Init == x = 0 /\ ToJsonArray(2)
Next == x' = x
====
