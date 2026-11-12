---- MODULE Spec ----
ZZ == 1 \star 2
---- MODULE I ----
CONSTANT F(_)
====
G(a, b) == a
M == INSTANCE I WITH F <- G
====
