---- MODULE M ----
EXTENDS Integers,TLC,Json
VARIABLE x
Init == x = 0
Next == x' = x /\ ToJsonObject(Print(7,2))
====
