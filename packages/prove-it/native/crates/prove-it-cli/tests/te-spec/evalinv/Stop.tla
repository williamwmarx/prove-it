---- MODULE Stop ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = x + 1
Inv == IF x = 1 THEN 1 ELSE TRUE
====
