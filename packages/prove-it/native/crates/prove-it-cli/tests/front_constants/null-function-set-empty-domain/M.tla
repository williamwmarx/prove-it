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
ASSUME PrintT(\E f \in [{} -> {N!A}] : TRUE)
====
