---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
ASSUME PrintT(LET F == [k \in 1..2 |-> k] IN IF PrintT(F) THEN F[0] ELSE 0)
Init == x = 0
Next == x' = x
====
