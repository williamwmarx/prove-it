---- MODULE M ----
EXTENDS Naturals
---- MODULE I ----
CONSTANT c
THEOREM T == /\ c = 1
             /\ TRUE
====
N == INSTANCE I WITH c <- 1
Q == INSTANCE I WITH c <- 1
ASSUME N!T!1 /\ Q!T
VARIABLE x
Init == x = 0
Next == x' = x
====
