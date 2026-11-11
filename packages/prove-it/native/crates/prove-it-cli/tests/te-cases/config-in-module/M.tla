---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
====
---- CONFIG M ----
INIT Init
NEXT Next
====
