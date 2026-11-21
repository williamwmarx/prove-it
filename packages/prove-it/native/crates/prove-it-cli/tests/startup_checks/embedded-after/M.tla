---- MODULE M ----
VARIABLE x
Init == x = 0
Next == x' = x
====
---- CONFIG M ----
INIT Init
NEXT Next
====
