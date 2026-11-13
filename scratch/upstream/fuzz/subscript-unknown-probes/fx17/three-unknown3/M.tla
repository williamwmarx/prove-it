---- MODULE M ----
VARIABLES x, y
Spec == x = 0 /\ y = 0 /\ [][x' = x /\ y' = y]_<<x, y>> /\ [][x' = x]_<<x, y>> /\ [][y' = y]_1
====
