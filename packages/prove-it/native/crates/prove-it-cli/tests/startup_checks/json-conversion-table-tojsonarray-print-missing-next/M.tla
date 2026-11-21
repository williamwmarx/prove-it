---- MODULE M ----
EXTENDS Integers,TLC,Json
VARIABLE x
Init == x = 0
Next == x' = x /\ ToJsonArray(Print(7,2))
====
