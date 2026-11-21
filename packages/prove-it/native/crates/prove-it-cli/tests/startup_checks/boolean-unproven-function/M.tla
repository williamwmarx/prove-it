---- MODULE M ----
ASSUME LET S == {x \in SUBSET {1}: TRUE} IN IF [v \in S |-> v] THEN TRUE ELSE TRUE
====
