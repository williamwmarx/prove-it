---- MODULE Spec ----
VARIABLE x
M == INSTANCE Inner WITH c <- 1
B == M!g[1, 2, 3]
====
