---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
K == PrintT("k")
Init == x = 0
Next == \/ x' = x + 1
        \/ LET a == 1 IN 2
====
