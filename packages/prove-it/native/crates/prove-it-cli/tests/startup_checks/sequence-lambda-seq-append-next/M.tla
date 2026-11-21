---- MODULE M ----
EXTENDS Integers, Sequences, TLC
VARIABLE x
Init == x = TRUE
Next == x' = PrintT(Append([i \in Seq({1}) |-> i],1))
====
