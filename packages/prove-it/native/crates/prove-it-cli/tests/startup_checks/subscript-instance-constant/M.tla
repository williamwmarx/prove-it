---- MODULE M ----
EXTENDS Naturals
CONSTANT K
VARIABLE v
---- MODULE Inner ----
VARIABLES v, c
ISpec == v = 0 /\ [][v' = v]_<<v, c>>
====
I(c) == INSTANCE Inner
Spec == I(K)!ISpec
====
