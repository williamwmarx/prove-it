---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
---- MODULE I ----
CONSTANT c
THEOREM V == c
====
N == INSTANCE I WITH c <- 1
ASSUME <<N!V,1>>[2] = 1
====
