---- MODULE M ----
EXTENDS Naturals
VARIABLE x
V(p) == L :: (p \div 0)
W(p) == LET a == 1 IN L :: (p \div 0)
Init == x = 0
Next == x' = W(2)!L + V(1)!L
====
