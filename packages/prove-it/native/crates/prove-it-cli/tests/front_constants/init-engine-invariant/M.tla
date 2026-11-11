---- MODULE M ----
VARIABLE x
Init == <<1>>[1] = 1
Next == x' = x
Inv == <<1>>[1] = 2
====
