---- MODULE M ----
EXTENDS Integers, Sequences, TLC
Test == PrintT(Append(IF TRUE THEN [i \in 1..2 |-> i] ELSE <<>>, 3))
ASSUME Test
====
