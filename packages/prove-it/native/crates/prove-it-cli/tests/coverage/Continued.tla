---- MODULE Continued ----
EXTENDS Naturals
VARIABLES x
Init == x \in 0..2
Next == x' = (x + 1) % 3
Inv == x # 1
====
