---- MODULE M ----
EXTENDS Integers,TLC,Json
ASSUME ToJsonArray({x \in SUBSET {1,2}: 1 \div 0 = 1}) = ""
====
