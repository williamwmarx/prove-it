---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
---- MODULE I ----
CONSTANT c
THEOREM A == c = 1
d == c
====
N == INSTANCE I WITH c <- 1
ASSUME N!A
====
