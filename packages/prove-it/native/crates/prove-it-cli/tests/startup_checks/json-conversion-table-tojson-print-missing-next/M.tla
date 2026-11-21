---- MODULE M ----
EXTENDS Integers,TLC,Json
VARIABLE x
Init == x = 0
Next == x' = x /\ ToJson(Print(7,2))
====
