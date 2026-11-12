---- MODULE Spec ----
---- MODULE I ----
CONSTANT F(_), G(_,_)
====
M == INSTANCE I WITH F <- Undefined, G <- Undefined
====
