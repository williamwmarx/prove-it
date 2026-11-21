---- MODULE M ----
EXTENDS Json, IOUtils, TLC, Naturals
---- MODULE I ----
CONSTANT c
THEOREM A == c
====
N == INSTANCE I WITH c <- 1
ASSUME Serialize(<<1>>, "out", N!A)
====
