---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLES x, y


Init == x = 0 /\ y = 0
Next == x' = x /\ y' = ((([a : {}, b : STRING] \ (Seq({1}) \X [{} -> Seq({1})])) \cup {"a"}) = ((SUBSET Nat \X (1..0)) \ (Int \X [(1..0) -> Int])))
====
