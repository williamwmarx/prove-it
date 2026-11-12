---- MODULE UnchangedInitUnassigned ----
VARIABLES x, y
Init == x = 0 /\ UNCHANGED y /\ y = 1
Next == UNCHANGED <<x, y>>
====
