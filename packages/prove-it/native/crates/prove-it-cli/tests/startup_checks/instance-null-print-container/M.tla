---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
---- MODULE I ----
CONSTANT c
THEOREM V == c
====
N == INSTANCE I WITH c <- 1
ASSUME PrintT(<<N!V>>)
====
