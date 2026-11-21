---- MODULE M ----
EXTENDS Naturals
ASSUME 1 \div 0 = 0
VARIABLE x
Init == x = 0
Next == x' = x
====
