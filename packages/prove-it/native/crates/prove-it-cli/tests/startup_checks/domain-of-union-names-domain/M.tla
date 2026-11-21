---- MODULE M ----
EXTENDS Naturals, Sequences, FiniteSets, TLC
VARIABLE x
Init == x = TRUE
Next == x' = (DOMAIN [y \in UNION {1, {2}} |-> y] = {})
====
