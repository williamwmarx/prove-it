---- MODULE M ----
EXTENDS I, Naturals
VARIABLE x
Init == x = 0
Next == UNCHANGED x
J == INSTANCE I WITH K <- 1
Inv == J!Ok
====
