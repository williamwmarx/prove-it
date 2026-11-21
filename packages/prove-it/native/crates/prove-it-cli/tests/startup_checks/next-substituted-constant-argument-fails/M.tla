---- MODULE M ----
EXTENDS Naturals
VARIABLE x
CONSTANT C(_)
Op(v) == x' = ~x
Init == x = FALSE
Next == C(1 \div 0)
====
