---- MODULE M ----
EXTENDS TLC, Integers, FiniteSets
VARIABLE x
ASSUME LET S == {"a"} IN 1 \in UNION {1..2,S}
Init == x = 0
Next == UNCHANGED x
====
