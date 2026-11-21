---- MODULE M ----
EXTENDS Integers, Sequences, TLC
VARIABLE x
Init == x = TRUE
Next == UNCHANGED x
Inv == PrintT(<<>> \o ([i \in STRING |-> i]))
====
