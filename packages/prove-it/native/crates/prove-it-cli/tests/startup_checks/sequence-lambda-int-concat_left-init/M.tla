---- MODULE M ----
EXTENDS Integers, Sequences, TLC
VARIABLE x
Init == x = PrintT(([i \in Int |-> i]) \o <<>>)
Next == UNCHANGED x
====
