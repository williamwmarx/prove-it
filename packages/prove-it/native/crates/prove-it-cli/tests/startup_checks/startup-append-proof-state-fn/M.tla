---- MODULE M ----
EXTENDS Integers, Sequences, TLC
VARIABLE x
Init == x = [i \in 1..2 |-> i]
Next == UNCHANGED x
Inv == Len(Append(x, 3)) > 0
====
