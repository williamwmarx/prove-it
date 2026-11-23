---- MODULE M ----
VARIABLE x
Init == x = 0
Next == x' = x
INSTANCE I WITH K <- 1
ASSUME P(0)
====
