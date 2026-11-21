---- MODULE Probe ----
EXTENDS TLC, Integers
INSTANCE Base WITH C <- 7
CONSTANT K, Foo
Unused == TLCSet(1, K) /\ ToString(K) = "2"
Unused2 == K
ASSUME TLCEval("Unused") = "Unused"
ASSUME PrintT(TLCGet(1))
====
