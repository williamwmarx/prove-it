---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE x
Init == x = \E t \in ({} \cap (Int \X {<<1>>[2]})) : TRUE
Next == UNCHANGED x
====
