---- MODULE M ----
EXTENDS Naturals, TLC
CONSTANT F(_)
VARIABLE x
Init == x = 0
Next == x' = F(Print(1 \div 0, x))
Inv == x < 5
====
