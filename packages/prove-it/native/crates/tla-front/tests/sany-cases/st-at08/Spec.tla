---- MODULE Spec ----
ZZ == 1 \star 2
---- MODULE I ----
CONSTANT F(_)
====
M == INSTANCE I WITH F <- @
====
