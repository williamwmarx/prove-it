---- MODULE Spec ----
VARIABLE x
---- MODULE In ----
g[a \in {1}, b \in {2}] == a
====
M == INSTANCE In
B == M!g[1,2,3]
====
