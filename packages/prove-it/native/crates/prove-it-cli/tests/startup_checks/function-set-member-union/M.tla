---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE x
Init == x = (<<1, 2>> \in ([Seq({1}) -> 1..0] \cup (Int \X {})))
Next == x' = x
====
