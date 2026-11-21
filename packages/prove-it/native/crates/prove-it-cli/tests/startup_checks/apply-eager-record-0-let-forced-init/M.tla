---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Init == x = (LET F == [k \in {} |-> k] IN IF PrintT(F) THEN F[0] ELSE 0)
Next == x' = x
====
