---- MODULE M ----
EXTENDS Integers, Sequences, TLC
Test == PrintT(Append(IF FALSE THEN <<>> ELSE [i \in 1..2 |-> i], 3))
ASSUME Test
====
