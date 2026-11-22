---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE y
Init == y = 0
Next == \E v \in (IF FALSE THEN (IF PrintT("bound") THEN {0, 1} ELSE {}) ELSE {0, 1}) : y' = v
====
