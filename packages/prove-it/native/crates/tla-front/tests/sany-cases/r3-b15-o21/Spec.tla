---- MODULE Spec ----
VARIABLE x
---- MODULE In ----
RECURSIVE r(_)
====
RECURSIVE t(_)
t(n) == n
B == LET RECURSIVE u(_) IN 1
====
