---- MODULE M ----
VARIABLES x, y
Spec == x = 0 /\ y = 0 /\ [][x' = x /\ y' = y]_x /\ [][x' = x]_<<x, y>>
====
