---- MODULE M ----
EXTENDS Integers, Sequences, TLC
VARIABLE x
Init == x = TRUE
Next == x' = PrintT(Tail([i \in STRING |-> i]))
====
