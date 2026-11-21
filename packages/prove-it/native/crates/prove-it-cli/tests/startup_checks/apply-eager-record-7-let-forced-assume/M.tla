---- MODULE M ----
EXTENDS Integers, TLC, FiniteSets
VARIABLE x
ASSUME PrintT(LET F == [k \in {v \in SUBSET {1}: TRUE} |-> k] IN IF PrintT(F) THEN F[{2}] ELSE 0)
Init == x = 0
Next == x' = x
====
