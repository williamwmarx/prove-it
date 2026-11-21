---- MODULE M ----
EXTENDS Integers,TLC,Json
CONSTANT F(_)
VARIABLE x
Init == x = 0 /\ ToJson(1 \div 0) = ""
Next == x' = x
====
