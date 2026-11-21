---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 0
Never == \E i \in (IF PrintT("split") THEN {} ELSE {1}) : TRUE
Next == (x < 2 /\ x' = x + 1) \/ Never
====
