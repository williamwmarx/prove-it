---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC, Randomization
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
E == [<<0, 1>> EXCEPT ![1] = 2]
Inv == E[3] = 0
====
