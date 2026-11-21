---- MODULE M ----
EXTENDS Integers, FiniteSets, Sequences, TLC
VARIABLE x
Bad == PrintT(Head(Seq({})))
Init == x = 0
Next == UNCHANGED x
====
