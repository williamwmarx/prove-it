---- MODULE Spec ----
---- MODULE I ----
CONSTANT F(_)
====
---- MODULE J ----
X(a) == 1
====
N == INSTANCE J
M == INSTANCE I WITH F <- N!X!Y
====
