---- MODULE M ----
EXTENDS TLC, Naturals, FiniteSets
---- MODULE I ----
CONSTANT c
THEOREM A == c
====
N == INSTANCE I WITH c <- 1
ASSUME {v \in {N!A} : TRUE} = {}
====
