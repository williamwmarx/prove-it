---- MODULE M ----
EXTENDS TLC, Sequences, Naturals
Foo(a) == a
I == INSTANCE fx
ASSUME PrintT(1)
====
