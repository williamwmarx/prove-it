---- MODULE M ----
EXTENDS Integers, Sequences, TLC
Test == PrintT(Append(CASE TRUE -> <<1>> [] OTHER -> <<2>>, 3))
ASSUME Test
====
