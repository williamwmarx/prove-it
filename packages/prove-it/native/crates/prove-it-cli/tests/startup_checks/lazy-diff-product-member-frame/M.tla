---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLES x, y


Init == x = 0 /\ y = 0
Next == x' = x /\ y' = (LET L == (Nat \X {x} \ {x} \X Nat) IN 1 \in L)
====
