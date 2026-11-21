---- MODULE M ----
EXTENDS Naturals, Sequences, FiniteSets, TLC
VARIABLE x
Init == x = (1 \in [r : {1, "a"}] \X {1})
Next == UNCHANGED x
====
