---- MODULE M ----
EXTENDS Integers, Sequences, TLC
Test == PrintT(Append(IF FALSE THEN <<1>> ELSE <<2>>, 3))
ASSUME Test
====
