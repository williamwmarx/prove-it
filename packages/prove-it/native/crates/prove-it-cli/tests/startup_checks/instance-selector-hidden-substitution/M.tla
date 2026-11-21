---- MODULE M ----
EXTENDS Naturals
---- MODULE I ----
CONSTANT c
THEOREM T == /\ c = 1
             /\ TRUE
====
N == INSTANCE I WITH c <- 1
ASSUME N!T /\ N!T!1
VARIABLE x
Init == x = 0
Next == x' = x
====
