---- MODULE M ----
EXTENDS Integers,TLC,Json
VARIABLE x
Init == x = 0 /\ ToJsonArray([a |-> 1]) = ""
Next == x' = x
====
