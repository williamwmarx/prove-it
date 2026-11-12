---- MODULE M ----
EXTENDS Naturals, Sequences, TLC
VARIABLE x
F(n) == 10 \div n
D == LET k == 0 IN F(k)
Init == x = 0
Next == x < 1 /\ x' = D
====
