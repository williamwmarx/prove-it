---- MODULE M ----
EXTENDS Naturals, TLC
---- MODULE Inner ----
CONSTANT S
Op == S /\ S
====
VARIABLE x
P(v) == PrintT(v)
I == INSTANCE Inner WITH S <- P(5)
Init == x = 0
Next == x' = x
ASSUME I!Op
====
