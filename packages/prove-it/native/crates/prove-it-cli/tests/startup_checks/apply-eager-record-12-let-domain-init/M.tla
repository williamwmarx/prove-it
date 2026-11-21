---- MODULE M ----
EXTENDS Integers, TLC, FiniteSets
VARIABLE x
Init == x = (LET F == [k \in DOMAIN [k \in 1..2 |-> k] |-> k] IN IF Cardinality(DOMAIN F) >= 0 THEN F[0] ELSE 0)
Next == x' = x
====
