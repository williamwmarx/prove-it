---- MODULE M ----
EXTENDS Integers,TLC,Json
VARIABLE x
Init == x = 0 /\ ToJson(1)
Next == x' = x
====
