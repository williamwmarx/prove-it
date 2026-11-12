---- MODULE Spec ----
VARIABLE x
M == INSTANCE Inner
THEOREM TRUE
BY DEF M!q, M, M!r
====
