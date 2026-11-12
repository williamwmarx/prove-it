---- MODULE Spec ----
---- MODULE I ----
CONSTANT F(_)
====
---- MODULE J ----
G(a) == a
====
N == INSTANCE J
M == INSTANCE I WITH F <- N!G!H
====
