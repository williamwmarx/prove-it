---- MODULE Spec ----
---- MODULE I ----
CONSTANT F(_), G(_)
====
---- MODULE J ----
X == 1
====
N == INSTANCE J
M == INSTANCE I WITH F <- N!H, G <- N!K
====
