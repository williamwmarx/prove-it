---- MODULE M ----
EXTENDS Naturals, TLC
---- MODULE I ----
CONSTANT c
THEOREM A == c
====
VARIABLE x
N == INSTANCE I WITH c <- 1
Init == x = 0
Next == x' = x
ASSUME \A v \in {N!A}, w \in {1 \div 0} : FALSE
====
