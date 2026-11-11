---- MODULE UnchangedInit ----
VARIABLE x
Init == x = 0 /\ UNCHANGED x
Next == x' = x
====
