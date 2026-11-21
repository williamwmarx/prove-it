---- MODULE M ----
EXTENDS Integers,TLC,Json
VARIABLE x
Init == x = 0 /\ ToJsonObject(3) = ""
Next == x' = x
====
