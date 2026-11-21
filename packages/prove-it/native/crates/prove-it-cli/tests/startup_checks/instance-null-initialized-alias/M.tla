---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
---- MODULE I ----
CONSTANT c
THEOREM A == c = 1
====
D == 1
N == INSTANCE I WITH c <- D
ASSUME N!A
====
