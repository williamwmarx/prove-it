---- MODULE M ----
EXTENDS Integers,TLC,Json
VARIABLE x
Init == x = 0
Next == x' = x /\ ToJsonArray(1 \div 0) = ""
====
