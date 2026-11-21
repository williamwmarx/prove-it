---- MODULE M ----
EXTENDS Integers,TLC,Json
VARIABLE x
Init == x = 0 /\ ToJsonArray({x \in SUBSET {1,2}: 1 \div 0 = 1}) = ""
Next == x' = x
====
