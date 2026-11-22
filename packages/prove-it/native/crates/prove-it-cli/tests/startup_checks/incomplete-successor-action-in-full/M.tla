---- MODULE M ----
VARIABLES x, y
Init == x = 0 /\ y = 0
Next == x' = 1 /\ (x = 0 \/ y' = 0)
====
