---- MODULE Spec ----
---- MODULE I ----
CONSTANT F(_)
====
G(a) == a
M == INSTANCE I WITH F <- G(1)
====
