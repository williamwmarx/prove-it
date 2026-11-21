---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
---- MODULE I ----
CONSTANT c
THEOREM A == c = 1
====
INSTANCE I WITH c <- 1
ASSUME A
====
