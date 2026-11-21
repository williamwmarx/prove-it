---- MODULE M ----
EXTENDS Integers, Sequences, TLC
Test == PrintT(Append(CASE FALSE -> <<1>> [] OTHER -> <<2>>, 3))
ASSUME Test
====
