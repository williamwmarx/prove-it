---- MODULE M ----
VARIABLES x, y
Spec == x = 0 /\ y = 0 /\ [][x' = x /\ y' = y]_<<x, y>> /\ [][x' = x]_x
====
