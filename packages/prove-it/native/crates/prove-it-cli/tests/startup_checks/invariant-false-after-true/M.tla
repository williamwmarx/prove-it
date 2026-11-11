---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
B == Print("b", TRUE)
F == Print("f", FALSE)
====
