---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
---- MODULE I ----
CONSTANT c
THEOREM A == c = 1
====
---- MODULE J ----
CONSTANT c
d == c
====
N == INSTANCE I WITH c <- 1
Other == INSTANCE J WITH c <- 1
ASSUME N!A
====
