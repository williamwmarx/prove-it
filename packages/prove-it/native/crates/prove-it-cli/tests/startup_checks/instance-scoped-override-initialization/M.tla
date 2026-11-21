---- MODULE M ----
EXTENDS TLC, Integers
N == INSTANCE reviewlib WITH c <- 9
Alt == TRUE
ASSUME N!T
VARIABLE x
Init == x = 0
Next == x' = x
====
