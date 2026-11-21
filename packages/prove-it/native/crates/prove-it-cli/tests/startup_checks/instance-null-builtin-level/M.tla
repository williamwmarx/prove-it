---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
---- MODULE I ----
CONSTANT F(_,_)
d == F({1},{2})
====
N == INSTANCE I WITH F <- \cup
ASSUME N!d = {1,2}
====
