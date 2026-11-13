---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLES x, y


Init == x = 0 /\ y = (({1} \ ([{} -> Seq({1})] \ [(1..0) -> SUBSET Nat])))
Next == x' = x /\ y' = y
====
