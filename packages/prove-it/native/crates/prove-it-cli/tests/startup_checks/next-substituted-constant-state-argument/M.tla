---- MODULE M ----
EXTENDS Naturals
VARIABLE x
CONSTANT C(_)
Op(v) == x' = v
Init == x = FALSE
Next == C(x)
====
