---- MODULE printing_before ----
EXTENDS Naturals, TLC
---- MODULE I ----
CONSTANT F(_,_)
d == F({1},{2})
====
P == PrintT("before")
M == INSTANCE I WITH F <- \cup
ASSUME M!d = {1,2}
====
