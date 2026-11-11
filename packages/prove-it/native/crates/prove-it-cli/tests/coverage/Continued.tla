---- MODULE Continued ----
EXTENDS Naturals
VARIABLES x
Init == x = 0
Next == x' = (x + 1) % 4
Inv == x # 2
====
