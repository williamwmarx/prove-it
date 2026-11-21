---- MODULE M ----
EXTENDS Integers
VARIABLES x
Init == x = 0
Next == x' = {1} /\ ~UNCHANGED <<x, x>>
====
