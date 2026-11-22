---- MODULE M ----
---- MODULE Inner ----
B(x) == 2
====
I == INSTANCE Inner
A == lab :: 1
B == 2
THEOREM TRUE BY DEF A!B(1)
THEOREM TRUE BY DEF I!B(1), A!lab(1), B
====
