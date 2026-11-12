---- MODULE Spec ----
ZZ == 1 \star 2
---- MODULE I ----
CONSTANT F(_)
====
G(a) == a
M == INSTANCE I WITH F <- G(1)
====
