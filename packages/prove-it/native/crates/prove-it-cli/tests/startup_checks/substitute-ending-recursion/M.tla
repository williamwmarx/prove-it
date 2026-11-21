---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC, Randomization
CONSTANT C
RECURSIVE Fact(_)
Fact(n) == IF n = 0 THEN 1 ELSE n * Fact(n - 1)
D == Fact(5)
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
Inv == x < 2 \/ C = 121
====
