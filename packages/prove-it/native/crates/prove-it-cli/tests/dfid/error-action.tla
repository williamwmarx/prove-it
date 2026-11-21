---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = x + 1
Prop == [][1 \div (1 - x') >= 0]_x
====
