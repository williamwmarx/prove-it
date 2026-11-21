---- MODULE M ----
EXTENDS Integers
VARIABLES x, y
Init == x = 0 /\ y = 0
Next == x' = {1} /\ UNCHANGED x /\ y' = 0
====
