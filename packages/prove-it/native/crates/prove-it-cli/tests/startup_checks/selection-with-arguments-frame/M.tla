---- MODULE M ----
EXTENDS Naturals, Sequences, FiniteSets, TLC
VARIABLE x
V(p) == L :: (p \div 0)
Init == x = (V(1)!L = 0)
Next == UNCHANGED x
====
