---- MODULE M ----
EXTENDS Integers, Sequences, TLC
Test == PrintT(Append(IF TRUE THEN [i \in {} |-> 1 \div 0] ELSE <<1>>, 3))
ASSUME Test
====
