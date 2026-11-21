---- MODULE configured_print_before ----
EXTENDS Naturals, TLC
---- MODULE I ----
CONSTANT F(_,_)
d == F({1},{2})
====
P == 0
M == INSTANCE I WITH F <- \cup
Q == PrintT("configured")
ASSUME M!d = {1,2}
====
