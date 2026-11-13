---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLES x, y


Init == x = 0 /\ y = 0
Next == x' = x /\ y' = ({} \notin ([a : SUBSET Nat, b : (1..0)] \cap (Nat \X [{} -> Nat])))
====
