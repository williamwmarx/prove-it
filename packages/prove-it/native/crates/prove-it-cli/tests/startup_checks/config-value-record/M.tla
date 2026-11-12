---- MODULE M ----
VARIABLE x
Init == x = 0
Next == x' = x
Inv == [b |-> 1, a |-> 2]
====
