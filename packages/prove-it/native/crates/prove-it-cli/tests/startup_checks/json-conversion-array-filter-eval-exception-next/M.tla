---- MODULE M ----
EXTENDS Integers,TLC,Json
VARIABLE x
Init == x = 0
Next == x' = x /\ ToJsonArray({x \in SUBSET {1,2}: 1 \div 0 = 1}) = ""
====
