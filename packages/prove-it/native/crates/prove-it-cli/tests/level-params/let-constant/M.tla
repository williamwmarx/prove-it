---- MODULE M ----
VARIABLE x
Init == x = 0
Next == x' = x
P == LET A == x IN TRUE
====
