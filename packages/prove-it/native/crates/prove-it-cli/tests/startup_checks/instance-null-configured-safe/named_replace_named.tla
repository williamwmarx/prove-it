---- MODULE named_replace_named ----
EXTENDS Naturals, TLC
---- MODULE I ----
CONSTANT F(_,_)
d == F({1},{2})
====
CONSTANT K
Safe == {1,2}
M == INSTANCE I WITH F <- \cup
ASSUME M!d = {1,2}
====
