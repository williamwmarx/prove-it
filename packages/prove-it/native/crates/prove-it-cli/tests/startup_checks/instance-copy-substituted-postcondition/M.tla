---- MODULE M ----
VARIABLE x
Init == x = 0
Next == x' = x
INSTANCE I WITH K <- "b"
====
