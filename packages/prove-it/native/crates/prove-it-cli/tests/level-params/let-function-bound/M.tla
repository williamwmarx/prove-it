---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = 1 - x
F(p) == LET f[i \in p] == i IN 1 \in DOMAIN f
H == F({x'})
====
