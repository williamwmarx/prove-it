---- MODULE DotViolated ----
EXTENDS Naturals
VARIABLE x
Init == x \in 1..2
Next == x' \in {x + 1, x + 2, x * 3}
Inv == x < 40
====
