---- MODULE M ----
VARIABLE x
Init == x /\ x = FALSE
Next == UNCHANGED x
====
