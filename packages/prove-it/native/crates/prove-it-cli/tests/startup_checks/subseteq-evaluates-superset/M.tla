---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLES x, y


Init == x = 0 /\ y = 0
Next == x' = x /\ y' = ([STRING -> (1..0)] \subseteq (BOOLEAN \ [SUBSET Nat -> [SUBSET Nat -> (1..0)]]))
====
