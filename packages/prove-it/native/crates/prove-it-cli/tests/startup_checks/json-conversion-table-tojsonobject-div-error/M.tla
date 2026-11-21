---- MODULE M ----
EXTENDS Integers,TLC,Json
VARIABLE x
Init == x = 0 /\ ToJsonObject(1 \div 0)
Next == x' = x
====
