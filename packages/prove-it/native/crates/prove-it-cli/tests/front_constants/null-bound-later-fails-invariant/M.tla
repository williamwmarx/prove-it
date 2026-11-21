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
Inv == \E v \in {N!A}, w \in {CHOOSE y \in {} : TRUE} : TRUE
====
