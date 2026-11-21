---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE s
Init == s = (CHOOSE p \in {q \in (1..1001) \X (1..1000) : TRUE} : TRUE)
Next == UNCHANGED s
====
