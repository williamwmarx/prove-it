---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE x
Init == x = ([t \in ({} \ [{Assert(FALSE, "a")} -> Int]) |-> 1] = <<>>)
Next == UNCHANGED x
====
