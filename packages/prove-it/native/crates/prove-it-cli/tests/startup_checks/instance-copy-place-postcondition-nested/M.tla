---- MODULE M ----
VARIABLE x
Init == x = 0
Next == x' = x
INSTANCE A WITH J <- 1
====
