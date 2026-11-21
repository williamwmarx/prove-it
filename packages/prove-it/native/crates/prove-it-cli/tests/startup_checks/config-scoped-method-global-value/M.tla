---- MODULE M ----
EXTENDS TLC, Sequences, Naturals
I == INSTANCE fx
ASSUME PrintT(I!Q(<<1, 2>>))
====
