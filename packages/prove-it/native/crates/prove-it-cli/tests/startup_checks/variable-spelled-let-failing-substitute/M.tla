---- MODULE M ----
EXTENDS Integers, TLC
CONSTANT C
D == LET x == 0 IN 1 \div x
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
====
