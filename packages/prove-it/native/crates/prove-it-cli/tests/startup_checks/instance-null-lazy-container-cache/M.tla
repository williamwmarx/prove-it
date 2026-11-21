---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
---- MODULE I ----
CONSTANT c
THEOREM V == c
====
N == INSTANCE I WITH c <- 1
H(x) == <<x,x>>[2][1] = 1
ASSUME H(IF PrintT(1) THEN <<N!V>> ELSE <<0>>)
====
