---- MODULE Probe ----
EXTENDS TLC
INSTANCE Base WITH C <- 7
B == 3
K == 0
ASSUME PrintT(K)
====
