---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Init == x = 1
Next == x' = 2
Inv == x < 2
Prop == []<>(x > 0)
====
