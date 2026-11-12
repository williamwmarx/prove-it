---- MODULE M ----
EXTENDS Naturals

VARIABLE v
---- MODULE Inner ----
VARIABLES v, c
ISpec == v = 0 /\ [][v' = v]_<<v, c>>
====
I(c) == INSTANCE Inner
Spec == I(7)!ISpec
====
