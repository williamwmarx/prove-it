---- MODULE Spec ----
---- MODULE I ----
CONSTANT F(_)
====
---- MODULE J ----
X == 1
====
N == INSTANCE J
INSTANCE I WITH F <- N!H
====
