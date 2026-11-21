---- MODULE M ----
EXTENDS Integers,TLC,Json
VARIABLE x
Init == x = 0 /\ ToJsonArray(1 \div 0)
Next == x' = x
====
