---- MODULE M ----
EXTENDS Naturals, TLC
---- MODULE Inner ----
EXTENDS TLC
CONSTANT S
Op == S /\ S
====
VARIABLE x
I == INSTANCE Inner WITH S <- PrintT(5)
Init == x = 0
Next == x' = x
ASSUME I!Op
====
