---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC, Randomization
CONSTANT C
RECURSIVE S(_)
S(n) == IF n = 0 THEN 0 ELSE S(n - 1) + 1
D == S(1000)
VARIABLE x
Init == x = 0
Next == x' = x
====
